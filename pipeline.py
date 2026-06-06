import asyncio
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Any

from claude_agent_sdk import (
    AssistantMessage,
    ClaudeAgentOptions,
    ClaudeSDKClient,
    ResultMessage,
    TextBlock,
    ToolUseBlock,
    create_sdk_mcp_server,
    tool,
)

ROOT = Path(__file__).resolve().parent

USAGE = """\
Usage: python pipeline.py <crate-path> [flags]

  <crate-path>  Path to a Rust crate directory under `benchmarks/code/`.
                Required.
                Examples:  benchmarks/code/starting_examples/add_one
                           benchmarks/code/num-integer-0.1.46/gcd_stein_u64

                The corresponding working `_modified` copy is created at
                benchmarks/<MODEL_NAME>/<parent>/<crate>_modified/, where
                MODEL_NAME is the CLAUDE_MODEL env var (default
                "claude-opus-4-7"). Different models' rewrites live in
                separate trees so they don't clobber each other.

Flags:
  --no-harvest    Skip the two pattern-harvest stages so the shared pattern
                  libraries stay frozen. Use when benchmarking models against
                  each other against a fixed library.
  --proof-only    Skip the upstream stages; restore the obligations file from
                  the snapshot captured by a prior full run, then run
                  `make_proof` (and `harvest_proof_patterns` if `--no-harvest`
                  is not set). Use for clean per-run measurement of the proof
                  stage in isolation.
  --continue      Used with --proof-only: skip the restore and run `make_proof`
                  against the current obligations file as-is, preserving any
                  partial proof and helper lemmas from prior runs. Logs are
                  suffixed `_proof_only_continue` so continued runs don't get
                  confused with fresh measurements.
"""


def parse_args(argv: list[str]) -> tuple[str | None, bool, bool, bool]:
    """Parse the positional <crate-path> and optional flags.
    Returns (path-or-None, harvest_enabled, proof_only, proof_only_continue)."""
    crate_path: str | None = None
    harvest_enabled = True
    proof_only = False
    proof_only_continue = False
    for arg in argv[1:]:
        if arg in ("-h", "--help"):
            print(USAGE)
            sys.exit(0)
        if arg == "--no-harvest":
            harvest_enabled = False
            continue
        if arg == "--proof-only":
            proof_only = True
            continue
        if arg == "--continue":
            proof_only_continue = True
            continue
        if arg.startswith("-"):
            print(f"Unknown flag: {arg}\n", file=sys.stderr)
            print(USAGE, file=sys.stderr)
            sys.exit(2)
        if crate_path is not None:
            print(f"Error: multiple crate paths given ({crate_path} and {arg})", file=sys.stderr)
            sys.exit(2)
        crate_path = arg
    if proof_only_continue and not proof_only:
        print("--continue requires --proof-only", file=sys.stderr)
        sys.exit(2)
    return crate_path, harvest_enabled, proof_only, proof_only_continue


_CRATE_FROM_CLI, HARVEST_ENABLED, PROOF_ONLY, PROOF_ONLY_CONTINUE = parse_args(sys.argv)
# Suffix appended to the run's log/stage-notes filenames when --proof-only is
# active, so continued runs don't get visually confused with fresh measurements.
# Set in main() once the mode is known.
MODE_SUFFIX = ""
if _CRATE_FROM_CLI is None:
    print(USAGE, file=sys.stderr)
    sys.exit(2)
RUST_CRATE = Path(_CRATE_FROM_CLI).resolve()
CRATE_NAME = RUST_CRATE.name

if not RUST_CRATE.is_dir():
    print(f"Crate not found: {_CRATE_FROM_CLI}", file=sys.stderr)
    sys.exit(2)

# Model name drives the per-model working-crate root. Defined here (early)
# so the WORKING_CRATE path can incorporate it. CLAUDE_MODEL env var overrides.
#MODEL_NAME = os.getenv("CLAUDE_MODEL", "claude-sonnet-4-6")
MODEL_NAME = os.getenv("CLAUDE_MODEL", "claude-opus-4-7")

# Source crates live under `benchmarks/code/<parent>/<crate>/`. The `_modified`
# working copy lands under `benchmarks/<MODEL_NAME>/<parent>/<crate>_modified/`
# — keyed by model so different models' rewrites don't clobber each other.
BENCHMARKS_DIR = ROOT / "benchmarks"
CODE_DIR = BENCHMARKS_DIR / "code"
try:
    _SOURCE_REL = RUST_CRATE.relative_to(CODE_DIR)
except ValueError:
    print(
        f"Crate path must be under benchmarks/code/. Got: {RUST_CRATE}",
        file=sys.stderr,
    )
    print(
        "All source benchmarks live under benchmarks/code/; e.g. "
        "benchmarks/code/num-integer-0.1.46/binomial_u64",
        file=sys.stderr,
    )
    sys.exit(2)
WORKING_CRATE = (BENCHMARKS_DIR / MODEL_NAME / _SOURCE_REL.parent
                 / (CRATE_NAME + "_modified"))

RUST_REWRITE_SKILL = ROOT / "skills" / "rewrite-rust-to-hax-compatible-rust.md"
PBT_SKILL = ROOT / "skills" / "generate_property_based_tests.md"
LEAN_OBLIGATIONS_SKILL = ROOT / "skills" / "generate_lean_obligations.md"
LEAN_PROOF_SKILL = ROOT / "skills" / "generate_lean_proof.md"
SELECT_EXAMPLES_SKILL = ROOT / "skills" / "select_relevant_proof_examples.md"
EQUIVALENCE_CHECK_SKILL = ROOT / "skills" / "equivalence_check.md"
HARVEST_REWRITE_PATTERNS_SKILL = ROOT / "skills" / "harvest_rewrite_patterns.md"
HARVEST_PROOF_PATTERNS_SKILL = ROOT / "skills" / "harvest_proof_patterns.md"
# Pattern libraries are shared across models — a single accumulated pool.
# Harvesting into them can be disabled per run (see HARVEST_ENABLED) so a
# frozen library can be used when benchmarking models against each other.
PROOF_PATTERNS_DIR = ROOT / "proof_patterns"
REWRITE_PATTERNS_DIR = ROOT / "rewrite_patterns"
# One JSON per crate naming the stage that halted the pipeline (a failed
# deterministic check or any non-zero stage). Overview only; cleared when a
# crate later completes a full run.
INCOMPLETE_STAGES_DIR = ROOT / "incomplete_stages"
DOCUMENTATION = RUST_CRATE / "README.md"
CHECK_TIMEOUT_SECONDS = int(os.getenv("CHECK_TIMEOUT_SECONDS", "300"))
PERMISSION_MODE = os.getenv("CLAUDE_PERMISSION_MODE", "bypassPermissions")

# --- Lean LSP MCP (lean-lsp-mcp) --------------------------------------------
# Pinned so a benchmark run isn't perturbed by an upstream release. Gives the
# obligations/proof agents the same incremental diagnostics + live goal state
# a human sees in VS Code, without a full `lake build` per iteration. Started
# as a second stdio MCP server alongside the in-process `pipeline` server, for
# the two Lean stages only.
LEAN_LSP_MCP_VERSION = "0.26.2"
# Read-only inspection tools the agent may call — the "see it like the editor"
# surface. Authoritative tool names for the pinned version.
LEAN_LSP_TOOLS = [
    "lean_diagnostic_messages",  # the red squiggles / Problems panel
    "lean_goal",                 # InfoView tactic state at a position
    "lean_term_goal",            # expected type at a term position
    "lean_hover_info",           # hover types / docs
    "lean_completions",          # identifier completion
    "lean_declaration_file",     # jump-to-definition source
    "lean_references",           # find references
    "lean_file_outline",         # file outline
]
# Disabled at the server (defense-in-depth: permission_mode=bypassPermissions
# would otherwise let the agent call them regardless of the allow-list). These
# either execute Lean / build — bypassing the pipeline's logged tools and the
# deterministic `lake build` ground-truth gate — or surface Mathlib lemmas the
# project deliberately does not import (re-introducing the hallucination tax).
# 8 allowed + 14 disabled == the full pinned-version tool set.
LEAN_LSP_DISABLED_TOOLS = [
    "lean_build", "lean_run_code", "lean_multi_attempt", "lean_verify",
    "lean_profile_proof", "lean_code_actions",
    "lean_leansearch", "lean_loogle", "lean_leanfinder",
    "lean_state_search", "lean_hammer_premise", "lean_local_search",
    "lean_get_widgets", "lean_get_widget_source",
]

HOME = Path.home()

TOOL_ENV = os.environ.copy()
TOOL_ENV["HOME"] = str(HOME)
TOOL_ENV["PATH"] = ":".join(
    [
        str(HOME / ".cargo" / "bin"),
        str(HOME / ".local" / "bin"),
        str(HOME / ".elan" / "bin"),
        TOOL_ENV.get("PATH", ""),
    ]
)
TOOL_ENV.setdefault("CARGO_HOME", str(HOME / ".cargo"))
TOOL_ENV.setdefault("RUSTUP_HOME", str(HOME / ".rustup"))
TOOL_ENV.setdefault("ELAN_HOME", str(HOME / ".elan"))

# How to launch the Lean LSP MCP server. Prefer a pinned, pre-installed
# `uv tool` entrypoint — a near-instant exec with no per-launch package
# resolution. On-demand `uvx` re-resolves the package on every spawn, which
# made the stdio server's startup race with the agent (the server sometimes
# wasn't registered before the first turn). Install the fast path with:
#     uv tool install lean-lsp-mcp==0.26.2
# If it isn't installed, fall back to `uvx` so the pipeline still works.
_lean_lsp_entrypoint = shutil.which("lean-lsp-mcp", path=TOOL_ENV["PATH"])
if _lean_lsp_entrypoint:
    LEAN_LSP_MCP_COMMAND = _lean_lsp_entrypoint
    LEAN_LSP_MCP_BASE_ARGS: list[str] = []
else:
    LEAN_LSP_MCP_COMMAND = "uvx"
    LEAN_LSP_MCP_BASE_ARGS = [f"lean-lsp-mcp@{LEAN_LSP_MCP_VERSION}"]

CURRENT_CRATE = RUST_CRATE
CURRENT_STAGE = "unknown"
RUN_TIMESTAMP = datetime.now().strftime("%Y%m%d-%H%M%S")
ATTEMPT_LOG_DIR: Path | None = None
ATTEMPT_COUNTER = 0
STAGE_NOTES: dict[str, str] = {}

# Snapshot of the public obligation statements taken at the end of the
# obligations stage and checked at the end of the proof stage. The proof
# agent may only *close* obligations (replace `sorry` with a real proof);
# deleting or weakening one is a soundness violation. See
# `_snapshot_obligations` and `_verify_obligations_preserved`.
_OBLIGATIONS_SNAPSHOT: dict[str, str] | None = None

STAGE_NUMBERS: dict[str, int] = {
    "make_pbt": 1,
    "rust_hax_lean": 2,
    "equivalence_check": 3,
    "select_examples": 4,
    "make_lean_obligations": 5,
    "make_proof": 6,
    "harvest_rewrite_patterns": 7,
    "harvest_proof_patterns": 8,
}

STATUS_SUFFIXES: dict[str, str] = {
    "patched": "patched",
    "no_changes": "no_changes",
    "written": "written",
    "error": "error",
}

MCP_SERVER_NAME = "pipeline"


@dataclass(frozen=True)
class PromptAssets:
    pbt_skill: str
    rust_rewrite_skill: str
    lean_obligations_skill: str
    lean_proof_skill: str
    select_examples_skill: str
    equivalence_check_skill: str
    documentation: str
    original_source: str


def read_file(path: str | Path) -> str:
    return Path(path).read_text(encoding="utf-8")


def load_prompt_assets() -> PromptAssets:
    documentation = DOCUMENTATION.read_text(encoding="utf-8") if DOCUMENTATION.exists() else ""
    return PromptAssets(
        pbt_skill=read_file(PBT_SKILL),
        rust_rewrite_skill=read_file(RUST_REWRITE_SKILL),
        lean_obligations_skill=read_file(LEAN_OBLIGATIONS_SKILL),
        lean_proof_skill=read_file(LEAN_PROOF_SKILL),
        select_examples_skill=read_file(SELECT_EXAMPLES_SKILL),
        equivalence_check_skill=read_file(EQUIVALENCE_CHECK_SKILL),
        documentation=documentation,
        original_source=read_file(RUST_CRATE / "src" / "lib.rs"),
    )


PROMPT_ASSETS = load_prompt_assets()


def copy_rust_crate() -> None:
    WORKING_CRATE.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["rm", "-rf", str(WORKING_CRATE)], check=True)
    subprocess.run(["cp", "-R", str(RUST_CRATE), str(WORKING_CRATE)], check=True)


def ensure_crate_setup() -> None:
    """Run setup_crate.bash on RUST_CRATE if it hasn't been set up yet.
    Idempotent: detects an already-setup crate via the presence of
    `proofs/lean/extraction/lakefile.toml`, and only runs the script when
    that marker is missing (so we don't clobber the obligations-stage
    registration in lakefile.toml on subsequent runs)."""
    lakefile = RUST_CRATE / "proofs" / "lean" / "extraction" / "lakefile.toml"
    if lakefile.exists():
        return
    setup_script = ROOT / "setup_crate.bash"
    if not setup_script.exists():
        print(f"[setup] WARNING: {setup_script} not found — cannot auto-setup crate", file=sys.stderr)
        return
    print(f"[setup] Crate not yet set up — running setup_crate.bash on {RUST_CRATE}")
    result = subprocess.run(
        ["bash", str(setup_script), str(RUST_CRATE)],
        env=TOOL_ENV,
        text=True,
    )
    if result.returncode != 0:
        print(f"[setup] setup_crate.bash failed with exit {result.returncode}", file=sys.stderr)
        sys.exit(result.returncode)
    print("[setup] Done.\n")


def safe_path(rel_path: str) -> Path:
    rel = Path(rel_path)
    if rel.is_absolute():
        raise ValueError(f"Absolute paths are not allowed: {rel_path}")

    resolved = (CURRENT_CRATE / rel).resolve()
    root = CURRENT_CRATE.resolve()

    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ValueError(f"Path escapes crate: {rel_path}") from exc

    return resolved


def _is_extracted_hax_module(rel_path: str) -> bool:
    """`proofs/lean/extraction/<package>.lean` — the Hax-generated Lean file
    that the rust_hax_lean stage produced. Detected as: a `.lean` file
    directly in `proofs/lean/extraction/` (not under `.lake/`) whose name
    does not end with `Obligations.lean` (those are companion proof files,
    written by us, not by Hax)."""
    parts = Path(rel_path).parts
    return (
        len(parts) == 4
        and parts[0] == "proofs"
        and parts[1] == "lean"
        and parts[2] == "extraction"
        and parts[3].endswith(".lean")
        and not parts[3].endswith("Obligations.lean")
    )


def _is_obligations_file(rel_path: str) -> bool:
    parts = Path(rel_path).parts
    return (
        len(parts) >= 4
        and parts[0] == "proofs"
        and parts[1] == "lean"
        and parts[2] == "extraction"
        and parts[-1].endswith("Obligations.lean")
    )


def stage_write_allowed(rel_path: str) -> tuple[bool, str]:
    """Per-stage restriction on which files agents may edit.

    - `make_proof` may only edit obligations files
      (`proofs/lean/extraction/*Obligations.lean`). Everything else is
      out-of-scope at this stage.
    - `make_lean_obligations` may edit anything *except* the extracted
      Hax module (`proofs/lean/extraction/<package>.lean`). The obligations
      stage may legitimately need to touch `lakefile.toml`, write helper
      files, etc. — only the Hax-generated Lean is off-limits.

    Why the extracted module is locked: it is Hax output, and editing it
    produces obligations / proofs that no longer correspond to what Hax
    actually generated from the Rust source — the soundness chain
    Rust → Hax → Lean breaks.

    Other stages have no such restriction at this layer.
    """
    if CURRENT_STAGE == "make_proof":
        if _is_obligations_file(rel_path):
            return True, ""
        return (
            False,
            f"make_proof may only edit `proofs/lean/extraction/*Obligations.lean`; "
            f"refused write to `{rel_path}`. The extracted module is Hax output "
            "and must not be edited — recover invariants Lean-side in the "
            "obligations file instead.",
        )

    if CURRENT_STAGE == "make_lean_obligations":
        if _is_extracted_hax_module(rel_path):
            return (
                False,
                f"make_lean_obligations must not edit the extracted Hax module "
                f"`{rel_path}`. That file is Hax output — editing it produces "
                "obligations that no longer correspond to what Hax generated "
                "from the Rust source. Use the obligations companion file "
                "(`*Obligations.lean`) for any state your theorems need.",
            )
        return True, ""

    return True, ""


def summarize_result(result: dict[str, Any]) -> dict[str, Any]:
    return {
        "ok": result["ok"],
        "returncode": result.get("returncode"),
        "stdout": result.get("stdout", ""),
        "stderr": result.get("stderr", ""),
    }


def get_attempt_log_dir() -> Path:
    global ATTEMPT_LOG_DIR
    if ATTEMPT_LOG_DIR is None:
        ATTEMPT_LOG_DIR = RUST_CRATE / "attempted_changes" / RUN_TIMESTAMP
        ATTEMPT_LOG_DIR.mkdir(parents=True, exist_ok=True)
    return ATTEMPT_LOG_DIR


WRITE_PLACEHOLDER_PATCH = "<<WRITE_WORKING_FILE>>"


class Tee:
    """Write-through to multiple streams. Used to mirror stdout into a file."""

    def __init__(self, *streams: Any) -> None:
        self._streams = streams

    def write(self, data: str) -> int:
        for s in self._streams:
            s.write(data)
            s.flush()
        return len(data)

    def flush(self) -> None:
        for s in self._streams:
            s.flush()


def log_tool_call(tool_name: str, summary: str) -> None:
    """Append a one-line record of a tool invocation. Independent of the
    structured per-attempt logging — gives flat visibility into reads,
    cargo runs, lake builds, etc., even when nothing was patched."""
    log_path = get_attempt_log_dir() / "tool_calls.log"
    ts = datetime.now().isoformat(timespec="seconds")
    stage_num = STAGE_NUMBERS.get(CURRENT_STAGE, 0)
    line = f"{ts}  stage{stage_num} {CURRENT_STAGE}  {tool_name}  {summary}\n"
    with log_path.open("a", encoding="utf-8") as f:
        f.write(line)


def _truncate(s: str, limit: int = 160) -> str:
    s = s.replace("\n", "\\n")
    return s if len(s) <= limit else s[:limit] + f"... [+{len(s) - limit} chars]"


def record_patch_attempt(
    *,
    stage_name: str,
    rel_path: str,
    patch: str,
    before: str,
    after: str | None,
    status: str,
    trigger_error: str = "",
    error: str | None = None,
    change_details: list[dict[str, str]] | None = None,
) -> None:
    global ATTEMPT_COUNTER

    ATTEMPT_COUNTER += 1
    stage_num = STAGE_NUMBERS.get(stage_name, 0)
    suffix = STATUS_SUFFIXES.get(status, status)
    dir_name = f"{ATTEMPT_COUNTER:04d}_stage{stage_num}_{stage_name}_{suffix}"
    attempt_dir = get_attempt_log_dir() / dir_name
    attempt_dir.mkdir(parents=True, exist_ok=True)

    target_ext = Path(rel_path).suffix or ".txt"
    is_write = patch == WRITE_PLACEHOLDER_PATCH

    metadata = {
        "attempt": ATTEMPT_COUNTER,
        "stage": stage_name,
        "stage_number": stage_num,
        "kind": "write" if is_write else "patch",
        "crate": str(CURRENT_CRATE),
        "path": rel_path,
        "status": status,
        "change_count": 0 if is_write else len(change_details or []),
        "trigger_error": trigger_error or None,
        "error": error,
        "timestamp": datetime.now().isoformat(timespec="seconds"),
    }

    (attempt_dir / "metadata.json").write_text(
        json.dumps(metadata, indent=2),
        encoding="utf-8",
    )
    if not is_write:
        (attempt_dir / "search_replace.txt").write_text(patch, encoding="utf-8")
    if trigger_error:
        (attempt_dir / "error_context.txt").write_text(trigger_error, encoding="utf-8")
    (attempt_dir / f"before{target_ext}").write_text(before, encoding="utf-8")
    if after is not None:
        (attempt_dir / f"after{target_ext}").write_text(after, encoding="utf-8")


def run_stage(command: list[str], cwd: Path) -> dict[str, Any]:
    try:
        result = subprocess.run(
            command,
            cwd=cwd,
            env=TOOL_ENV,
            capture_output=True,
            text=True,
            timeout=CHECK_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as exc:
        return {
            "ok": False,
            "returncode": None,
            "stdout": exc.stdout or "",
            "stderr": f"Timed out after {CHECK_TIMEOUT_SECONDS}s",
        }
    except FileNotFoundError as exc:
        return {
            "ok": False,
            "returncode": None,
            "stdout": "",
            "stderr": str(exc),
        }

    return {
        "ok": result.returncode == 0,
        "returncode": result.returncode,
        "stdout": result.stdout,
        "stderr": result.stderr,
    }


def _verify_stage_postconditions(
    stage_name: str, checks: list[tuple[list[str], Path, str]]
) -> int:
    """After an agent stage finishes, re-run the same commands the agent was
    supposed to make pass. If any returns non-zero, print a clear
    `Couldn't pass phase: <stage_name>` message with the failing command,
    its exit code, and the tail of stderr — then return 1 so the main loop
    halts the pipeline.

    `checks` is a list of `(command, cwd, label)` triples. Commands run
    sequentially; the first failure aborts."""
    for cmd, cwd, label in checks:
        print(f"[verify {stage_name}] running: {label}")
        result = run_stage(cmd, cwd)
        if not result["ok"]:
            print(
                f"\nCouldn't pass phase: {stage_name} — {label} failed",
                file=sys.stderr,
            )
            print(f"  command: {' '.join(cmd)}", file=sys.stderr)
            print(f"  cwd:     {cwd}", file=sys.stderr)
            rc = result.get("returncode")
            if rc is not None:
                print(f"  exit:    {rc}", file=sys.stderr)
            stderr = (result.get("stderr") or "").strip()
            if stderr:
                tail = stderr.splitlines()[-20:]
                print("  stderr (last 20 lines):", file=sys.stderr)
                for line in tail:
                    print(f"    {line}", file=sys.stderr)
            return 1
    print(f"[verify {stage_name}] all checks passed")
    return 0


def apply_patch_to_text(original: str, patch: str) -> tuple[str, list[dict[str, str]]]:
    pattern = re.compile(
        r"<<< SEARCH\r?\n(.*?)\r?\n===\r?\n(.*?)\r?\n>>> REPLACE",
        re.DOTALL,
    )

    if not patch.strip():
        raise ValueError("Patch is empty")

    matches = list(pattern.finditer(patch))
    if not matches:
        if any(marker in patch for marker in ("<<< SEARCH", "===", ">>> REPLACE")):
            raise ValueError(
                "Patch format is invalid. Expected blocks like:\n"
                "<<< SEARCH\nold text\n===\nnew text\n>>> REPLACE"
            )
        raise ValueError("No patch blocks found in patch input")

    updated = original
    change_details: list[dict[str, str]] = []

    for idx, match in enumerate(matches, start=1):
        search = match.group(1)
        replace = match.group(2)

        if search not in updated:
            raise ValueError(f"Search block {idx} not found:\n{search}")

        updated = updated.replace(search, replace, 1)
        change_details.append(
            {
                "index": str(idx),
                "before": search,
                "after": replace,
            }
        )

    return updated, change_details


def parse_lake_package_name(extraction_dir: Path) -> str | None:
    lakefile = extraction_dir / "lakefile.toml"
    if not lakefile.exists():
        return None

    contents = lakefile.read_text(encoding="utf-8")
    match = re.search(r"^name\s*=\s*\"([^\"]+)\"", contents, flags=re.MULTILINE)
    if not match:
        return None
    return match.group(1)


def list_extraction_lean_files(extraction_dir: Path) -> list[Path]:
    return sorted(
        path
        for path in extraction_dir.rglob("*.lean")
        if ".lake" not in path.parts
    )


def render_extraction_files(extraction_dir: Path) -> str:
    parts = []
    for path in list_extraction_lean_files(extraction_dir):
        rel = path.relative_to(extraction_dir)
        body = path.read_text(encoding="utf-8")
        parts.append(f"=== proofs/lean/extraction/{rel} ===\n{body}")
    return "\n\n".join(parts) if parts else "(no .lean files found)"


def companion_obligations_module_name(package_name: str) -> str:
    """Convention: 'square' -> 'SquareObligations', 'gcd' -> 'GcdObligations'."""
    return f"{package_name[:1].upper()}{package_name[1:]}Obligations"


def prepare_obligations_scaffold(crate: Path) -> None:
    """Pre-create the obligations companion `.lean` file and register it in
    `lakefile.toml`. Idempotent — safe to call multiple times. The agent in the
    obligations stage then only has to fill in `theorem` statements, not figure
    out imports or wire up Lake."""
    extraction_dir = crate / "proofs" / "lean" / "extraction"
    if not extraction_dir.exists():
        print(f"[scaffold] {extraction_dir} not found; skipping (run hax first)")
        return

    package_name = parse_lake_package_name(extraction_dir)
    if package_name is None:
        print(f"[scaffold] could not parse package name from {extraction_dir}/lakefile.toml; skipping")
        return

    companion_module = companion_obligations_module_name(package_name)
    companion_path = extraction_dir / f"{companion_module}.lean"
    lakefile = extraction_dir / "lakefile.toml"

    if not companion_path.exists():
        scaffold = (
            f"-- Companion obligations file for the `{package_name}` extraction.\n"
            f"-- Each property the Rust function should satisfy belongs here as a separate `theorem`.\n"
            f"-- Proofs use `sorry` placeholders at this stage; they are filled in by the proof stage.\n"
            f"\n"
            f"import Hax\n"
            f"import Std.Tactic.Do\n"
            f"import Std.Do.Triple\n"
            f"import Std.Tactic.Do.Syntax\n"
            f"import {package_name}\n"
            f"\n"
            f"open Std.Do\n"
            f"open Std.Tactic\n"
            f"\n"
            f"set_option mvcgen.warning false\n"
            f"set_option linter.unusedVariables false\n"
            f"\n"
            f"namespace {companion_module}\n"
            f"\n"
            f"-- Add `theorem` declarations below.\n"
            f"\n"
            f"end {companion_module}\n"
        )
        companion_path.write_text(scaffold, encoding="utf-8")
        print(f"[scaffold] created {companion_path.relative_to(crate)}")

    contents = lakefile.read_text(encoding="utf-8")
    if f'name = "{companion_module}"' in contents:
        return  # already registered

    old_default = f'defaultTargets = ["{package_name}"]'
    new_default = f'defaultTargets = ["{package_name}", "{companion_module}"]'
    if old_default in contents:
        contents = contents.replace(old_default, new_default, 1)
    else:
        print(f"[scaffold] WARNING: could not find {old_default!r} in lakefile to extend")

    if not contents.endswith("\n"):
        contents += "\n"
    contents += f'\n[[lean_lib]]\nname = "{companion_module}"\n'

    lakefile.write_text(contents, encoding="utf-8")
    print(f"[scaffold] registered {companion_module} in {lakefile.relative_to(crate)}")


def find_primary_extracted_lean_file(extraction_dir: Path) -> Path:
    candidates = [
        path
        for path in extraction_dir.rglob("*.lean")
        if ".lake" not in path.parts
    ]

    if not candidates:
        raise FileNotFoundError(f"No Lean files found under {extraction_dir}")

    package_name = parse_lake_package_name(extraction_dir)
    if package_name is not None:
        expected_name = f"{package_name}.lean"
        for candidate in candidates:
            if candidate.name == expected_name:
                return candidate

    top_level_candidates = [path for path in candidates if path.parent == extraction_dir]
    if top_level_candidates:
        return sorted(top_level_candidates, key=lambda path: path.name)[0]

    return sorted(candidates, key=lambda path: (len(path.parts), str(path)))[0]


def _mcp_text(text: str) -> dict[str, Any]:
    return {"content": [{"type": "text", "text": text}]}


@tool(
    "write_working_file",
    "Create or overwrite a UTF-8 text file relative to the current crate.",
    {
        "type": "object",
        "properties": {
            "path": {
                "type": "string",
                "description": "Path to the file to create or overwrite",
            },
            "content": {
                "type": "string",
                "description": "Full UTF-8 file content to write",
            },
            "overwrite": {
                "type": "boolean",
                "description": "Set true to overwrite existing file content",
                "default": False,
            },
            "error_message": {
                "type": "string",
                "description": "Non-empty error context that motivated this write",
            },
        },
        "required": ["path", "content", "error_message"],
    },
)
async def write_working_file_tool(args: dict[str, Any]) -> dict[str, Any]:
    path = args["path"]
    content = args["content"]
    overwrite = bool(args.get("overwrite", False))
    error_message = args.get("error_message", "") or ""
    log_tool_call("write_working_file", f"path={path} bytes={len(content)} overwrite={overwrite}")

    normalized_error_message = error_message.strip()
    if not normalized_error_message:
        record_patch_attempt(
            stage_name=CURRENT_STAGE,
            rel_path=path,
            patch=WRITE_PLACEHOLDER_PATCH,
            before="",
            after=None,
            status="error",
            trigger_error="",
            error="error_message is required and must be non-empty",
        )
        return _mcp_text("ERROR: error_message is required and must be non-empty")

    stage_ok, stage_reason = stage_write_allowed(path)
    if not stage_ok:
        record_patch_attempt(
            stage_name=CURRENT_STAGE,
            rel_path=path,
            patch=WRITE_PLACEHOLDER_PATCH,
            before="",
            after=None,
            status="error",
            trigger_error=normalized_error_message,
            error=stage_reason,
        )
        return _mcp_text(f"ERROR: {stage_reason}")

    existing = ""
    try:
        resolved = safe_path(path)
        existing = resolved.read_text(encoding="utf-8") if resolved.exists() else ""

        if resolved.exists() and not overwrite:
            record_patch_attempt(
                stage_name=CURRENT_STAGE,
                rel_path=path,
                patch=WRITE_PLACEHOLDER_PATCH,
                before=existing,
                after=None,
                status="error",
                trigger_error=normalized_error_message,
                error="file exists and overwrite=false",
            )
            return _mcp_text(
                f"ERROR: {path} already exists; set overwrite=true to replace it"
            )

        resolved.parent.mkdir(parents=True, exist_ok=True)
        resolved.write_text(content, encoding="utf-8")

        record_patch_attempt(
            stage_name=CURRENT_STAGE,
            rel_path=path,
            patch=WRITE_PLACEHOLDER_PATCH,
            before=existing,
            after=content,
            status="written",
            trigger_error=normalized_error_message,
        )

        action = "overwritten" if existing else "created"
        return _mcp_text(f"OK: {action} {path}")

    except Exception as exc:
        record_patch_attempt(
            stage_name=CURRENT_STAGE,
            rel_path=path,
            patch=WRITE_PLACEHOLDER_PATCH,
            before=existing,
            after=None,
            status="error",
            trigger_error=normalized_error_message,
            error=str(exc),
        )
        return _mcp_text(f"ERROR: {exc}")


@tool(
    "apply_file_patch_tool",
    "Apply a patch to a single file using '<<< SEARCH', '===', '>>> REPLACE' blocks. Always include the error context that motivated the patch.",
    {
        "type": "object",
        "properties": {
            "path": {
                "type": "string",
                "description": "Path to the file to modify",
            },
            "patch": {
                "type": "string",
                "description": "Patch describing the change to apply",
            },
            "error_message": {
                "type": "string",
                "description": "Non-empty error context that motivated this patch attempt",
            },
        },
        "required": ["path", "patch", "error_message"],
    },
)
async def apply_file_patch_tool_tool(args: dict[str, Any]) -> dict[str, Any]:
    path = args["path"]
    patch = args["patch"]
    log_tool_call("apply_file_patch_tool", f"path={path} patch_bytes={len(patch)}")
    error_message = args.get("error_message", "") or ""

    normalized_error_message = error_message.strip()
    if not normalized_error_message:
        record_patch_attempt(
            stage_name=CURRENT_STAGE,
            rel_path=path,
            patch=patch,
            before="",
            after=None,
            status="error",
            trigger_error="",
            error="error_message is required and must be non-empty",
        )
        return _mcp_text("ERROR: error_message is required and must be non-empty")

    stage_ok, stage_reason = stage_write_allowed(path)
    if not stage_ok:
        record_patch_attempt(
            stage_name=CURRENT_STAGE,
            rel_path=path,
            patch=patch,
            before="",
            after=None,
            status="error",
            trigger_error=normalized_error_message,
            error=stage_reason,
        )
        return _mcp_text(f"ERROR: {stage_reason}")

    original = ""
    try:
        resolved = safe_path(path)
        original = resolved.read_text(encoding="utf-8") if resolved.exists() else ""

        updated, change_details = apply_patch_to_text(original, patch)

        if updated == original:
            record_patch_attempt(
                stage_name=CURRENT_STAGE,
                rel_path=path,
                patch=patch,
                before=original,
                after=updated,
                status="no_changes",
                trigger_error=normalized_error_message,
                change_details=change_details,
            )
            return _mcp_text(f"OK: no changes for {path}")

        resolved.parent.mkdir(parents=True, exist_ok=True)
        resolved.write_text(updated, encoding="utf-8")

        record_patch_attempt(
            stage_name=CURRENT_STAGE,
            rel_path=path,
            patch=patch,
            before=original,
            after=updated,
            status="patched",
            trigger_error=normalized_error_message,
            change_details=change_details,
        )

        return _mcp_text(f"OK: patched {path}")

    except Exception as exc:
        record_patch_attempt(
            stage_name=CURRENT_STAGE,
            rel_path=path,
            patch=patch,
            before=original,
            after=None,
            status="error",
            trigger_error=normalized_error_message,
            error=str(exc),
        )
        return _mcp_text(f"ERROR: {exc}")


@tool(
    "run_cargo_test",
    "Run cargo test in the current crate.",
    {"type": "object", "properties": {}},
)
async def run_cargo_test_tool(args: dict[str, Any]) -> dict[str, Any]:
    result = run_stage(["cargo", "test"], CURRENT_CRATE)
    log_tool_call("run_cargo_test", f"ok={result['ok']} rc={result.get('returncode')}")
    return _mcp_text(json.dumps(summarize_result(result)))


@tool(
    "run_cargo_hax_into_lean",
    "Run cargo hax into lean in the working crate.",
    {"type": "object", "properties": {}},
)
async def run_cargo_hax_into_lean_tool(args: dict[str, Any]) -> dict[str, Any]:
    result = run_stage(["cargo", "hax", "into", "lean"], WORKING_CRATE)
    log_tool_call("run_cargo_hax_into_lean", f"ok={result['ok']} rc={result.get('returncode')}")
    return _mcp_text(json.dumps(summarize_result(result)))


@tool(
    "run_lake_build",
    "Run lake build in proofs/lean/extraction.",
    {"type": "object", "properties": {}},
)
async def run_lake_build_tool(args: dict[str, Any]) -> dict[str, Any]:
    result = run_stage(
        ["lake", "build"],
        WORKING_CRATE / "proofs" / "lean" / "extraction",
    )
    log_tool_call("run_lake_build", f"ok={result['ok']} rc={result.get('returncode')}")
    return _mcp_text(json.dumps(summarize_result(result)))


_REWRITE_PATTERN_NAME = re.compile(r"^[a-z][a-z0-9_]*\.rs$")


@tool(
    "write_rewrite_pattern",
    "Create or overwrite a file in the repo-root `rewrite_patterns/` archive "
    "documenting a Hax-incompatible pattern (snake_case .rs filename).",
    {
        "type": "object",
        "properties": {
            "name": {
                "type": "string",
                "description": "File name like 'bool_to_int_cast.rs' — snake_case, must end in .rs, no slashes.",
            },
            "content": {
                "type": "string",
                "description": "Full file body. Convention: `// unsupported: <reason>` then `// before` then code; "
                "optionally followed by `// after` then the Hax-compatible rewrite.",
            },
        },
        "required": ["name", "content"],
    },
)
async def write_rewrite_pattern_tool(args: dict[str, Any]) -> dict[str, Any]:
    try:
        name = args["name"]
        if not _REWRITE_PATTERN_NAME.match(name):
            return _mcp_text(
                f"ERROR: name must match [a-z][a-z0-9_]*\\.rs: {name!r}"
            )
        REWRITE_PATTERNS_DIR.mkdir(parents=True, exist_ok=True)
        dest = REWRITE_PATTERNS_DIR / name
        dest.write_text(args["content"], encoding="utf-8")
        log_tool_call("write_rewrite_pattern", f"name={name} bytes={len(args['content'])}")
        return _mcp_text(f"OK: wrote rewrite_patterns/{name}")
    except Exception as exc:
        return _mcp_text(f"ERROR: {exc}")


_VALID_PROOF_PATTERN_NAME = re.compile(r"^[a-z][a-z0-9_]*$")


@tool(
    "add_proof_pattern",
    "Promote the current working crate into the `proof_patterns/` library. "
    "Copies WORKING_CRATE into `proof_patterns/<name>/`, strips build artifacts, "
    "and writes its `manifest.json` from the supplied `features` + `summary`. "
    "Call at most once per session.",
    {
        "type": "object",
        "properties": {
            "name": {
                "type": "string",
                "description": "Snake-case folder name. Default = working crate leaf name.",
            },
            "features": {
                "type": "array",
                "items": {"type": "string"},
                "description": "Manifest `features` list — lower-case hyphenated proof-obstacle tags.",
            },
            "summary": {
                "type": "string",
                "description": "Manifest `summary` — one-line description of what the example teaches.",
            },
        },
        "required": ["name", "features", "summary"],
    },
)
async def add_proof_pattern_tool(args: dict[str, Any]) -> dict[str, Any]:
    try:
        name = args["name"]
        if not _VALID_PROOF_PATTERN_NAME.match(name):
            return _mcp_text(f"ERROR: name must match [a-z][a-z0-9_]*: {name!r}")
        features = args["features"]
        summary = args["summary"]
        if not isinstance(features, list) or not all(isinstance(t, str) for t in features):
            return _mcp_text("ERROR: features must be a list of strings")
        if not isinstance(summary, str) or not summary.strip():
            return _mcp_text("ERROR: summary must be a non-empty string")

        PROOF_PATTERNS_DIR.mkdir(parents=True, exist_ok=True)
        dest = PROOF_PATTERNS_DIR / name
        subprocess.run(["rm", "-rf", str(dest)], check=True)
        subprocess.run(["cp", "-R", str(WORKING_CRATE), str(dest)], check=True)
        for rel in ["target", "Cargo.lock"]:
            subprocess.run(["rm", "-rf", str(dest / rel)], check=False)
        extraction = dest / "proofs" / "lean" / "extraction"
        subprocess.run(["rm", "-rf", str(extraction / ".lake")], check=False)
        subprocess.run(["rm", "-f", str(extraction / "lake-manifest.json")], check=False)

        manifest = {"features": features, "summary": summary}
        (dest / "manifest.json").write_text(
            json.dumps(manifest, indent=2) + "\n",
            encoding="utf-8",
        )
        log_tool_call(
            "add_proof_pattern",
            f"name={name} features={len(features)} summary_bytes={len(summary)}",
        )
        return _mcp_text(f"OK: installed {dest.relative_to(ROOT)} with {len(features)} feature tag(s)")
    except Exception as exc:
        return _mcp_text(f"ERROR: {exc}")


ALL_TOOLS = [
    write_working_file_tool,
    apply_file_patch_tool_tool,
    run_cargo_test_tool,
    run_cargo_hax_into_lean_tool,
    run_lake_build_tool,
    write_rewrite_pattern_tool,
    add_proof_pattern_tool,
]


def mcp_tool_name(short_name: str) -> str:
    return f"mcp__{MCP_SERVER_NAME}__{short_name}"


def make_pbt_prompt() -> str:
    return f"""{PROMPT_ASSETS.pbt_skill}

Original src/lib.rs for reference:

{PROMPT_ASSETS.original_source}
"""


def render_example_sources() -> str:
    """List paths to example crates' src/lib.rs files. Used by the rewrite
    stage so the agent can consult how prior targets handled Hax-rewrite
    patterns (loop_decreases, .abs() inlining, etc.) before exploring the
    Hax prelude. Paths-only — agent reads on demand."""
    if not PROOF_PATTERNS_DIR.exists():
        return ""
    sources = sorted(PROOF_PATTERNS_DIR.glob("*/src/lib.rs"))
    if not sources:
        return ""
    return "\n".join(f"- {p}" for p in sources)


def render_rewrite_patterns() -> str:
    """Inline the contents of every `rewrite_patterns/*.rs` file. These are
    short (10-20 lines each), so embedding them in the prompt avoids a
    cold-start `Glob` + `Read` round-trip for every rewrite session."""
    if not REWRITE_PATTERNS_DIR.exists():
        return ""
    files = sorted(REWRITE_PATTERNS_DIR.glob("*.rs"))
    if not files:
        return ""
    sections = []
    for p in files:
        sections.append(f"### `rewrite_patterns/{p.name}`\n\n```rust\n{p.read_text(encoding='utf-8').strip()}\n```")
    return "\n\n".join(sections)


def rewrite_to_lean_prompt() -> str:
    example_sources = render_example_sources()
    examples_section = (
        f"""

Reference example sources — Rust files from previously-verified crates. **Read these on demand** before exploring the Hax prelude when you encounter a pattern that needs rewriting (library calls, `while` loops, etc.). Each shows how a prior target was made Hax-compatible:

{example_sources}
"""
        if example_sources
        else ""
    )
    patterns = render_rewrite_patterns()
    patterns_section = (
        f"""

## Known Hax-incompatibility patterns (archive)

The following are documented Hax / `lake build` failures and their proven rewrites. **Consult these first** whenever `run_cargo_hax_into_lean` or `run_lake_build` produces an error — match the error stderr against each `// unsupported:` header, and if one matches, apply the corresponding `// after` shape directly instead of investigating from scratch. Each pattern has been verified end-to-end (cargo test + Hax + lake build all pass post-rewrite).

{patterns}
"""
        if patterns
        else ""
    )
    return f"""{PROMPT_ASSETS.rust_rewrite_skill}{examples_section}{patterns_section}

Original src/lib.rs for reference:

{PROMPT_ASSETS.original_source}
"""


def _documentation_section() -> str:
    doc = PROMPT_ASSETS.documentation.strip()
    return f"\nDocumentation:\n{doc}\n" if doc else ""


def make_lean_obligations_prompt() -> str:
    working_source = read_file(WORKING_CRATE / "src" / "lib.rs")
    extraction_dir = WORKING_CRATE / "proofs" / "lean" / "extraction"
    extracted_lean = render_extraction_files(extraction_dir)
    package_name = parse_lake_package_name(extraction_dir) or "<unknown>"
    companion_module = companion_obligations_module_name(package_name)
    selector_notes = STAGE_NOTES.get("select_examples", "").strip()
    selected_paths = render_selected_example_paths(selector_notes) if selector_notes else ""
    if selected_paths:
        examples_section = f"""

Reference examples — closed-proof obligations files from past targets that the selection stage flagged as structurally similar. **Read at least the first one before deciding what theorem statements to write.** Their statement shapes (precondition form, postcondition form, failure-case form) are likely transferable; copying the shape is almost always faster than rediscovering it from Hax prelude internals.

{selected_paths}

Selector's rationale (why these were picked, what each example covers, gaps in the library):

{selector_notes}
"""
    elif selector_notes:
        examples_section = f"""

Selector's notes (no obligations files were inlined — selector found no usable matches):

{selector_notes}
"""
    else:
        examples_section = ""
    return f"""{PROMPT_ASSETS.lean_obligations_skill}
{_documentation_section()}{examples_section}
Working src/lib.rs (Rust source under verification):
{working_source}

The companion obligations file `proofs/lean/extraction/{companion_module}.lean` has already been created and registered in `lakefile.toml`. It has the right imports (`Hax`, `Std.Tactic.Do`, `Std.Do.Triple`, `Std.Tactic.Do.Syntax`, `{package_name}`), opens `Std.Do` and `Std.Tactic`, and wraps everything in `namespace {companion_module}`. Edit it via `apply_file_patch_tool`. Do not edit the extracted module `{package_name}.lean` and do not modify `lakefile.toml`.

Current Lean files in proofs/lean/extraction/:
{extracted_lean}
"""


# Match `proof_patterns/<name>` from the selector's free-form output. Leaf
# names may start with a digit (`000_has_close_elements_modified`), so the
# capture class is `\w+`; the original `[A-Za-z_]…` form silently dropped
# every digit-leading example.
SELECTED_EXAMPLE_PATTERN = re.compile(r"\bproof_patterns/(\w+)\b")


def render_examples_manifests() -> str:
    if not PROOF_PATTERNS_DIR.exists():
        return "(No proof_patterns library yet — `proof_patterns/` directory does not exist. Return zero picks.)"
    manifests = sorted(PROOF_PATTERNS_DIR.glob("*/manifest.json"))
    if not manifests:
        return "(`proof_patterns/` exists but contains no manifest.json files. Return zero picks.)"
    parts = []
    for path in manifests:
        rel = path.relative_to(ROOT)
        parts.append(f"=== {rel} ===\n{path.read_text(encoding='utf-8')}")
    return "\n\n".join(parts)


def find_obligations_file_in(extraction_dir: Path) -> Path | None:
    if not extraction_dir.exists():
        return None
    candidates = sorted(
        p for p in extraction_dir.glob("*Obligations.lean")
        if ".lake" not in p.parts
    )
    return candidates[0] if candidates else None


def parse_selected_examples(selector_output: str) -> list[Path]:
    """Extract `proof_patterns/<name>` paths from the selector's free-form output.
    De-duplicates, validates the directory exists, caps at 5."""
    seen: set[str] = set()
    paths: list[Path] = []
    for match in SELECTED_EXAMPLE_PATTERN.finditer(selector_output):
        name = match.group(1)
        if name in seen:
            continue
        seen.add(name)
        candidate = PROOF_PATTERNS_DIR / name
        if candidate.is_dir():
            paths.append(candidate)
        if len(paths) >= 5:
            break
    return paths


def render_selected_example_paths(selector_output: str) -> str:
    """List absolute paths to the obligations files of selected examples,
    one per line. Used to point the proof agent at references to Read on
    demand (paths-only mode — content is not inlined to keep the prompt small)."""
    paths = parse_selected_examples(selector_output)
    if not paths:
        return ""
    parts = []
    for path in paths:
        oblig = find_obligations_file_in(path / "proofs" / "lean" / "extraction")
        if oblig is None:
            continue
        parts.append(f"- {oblig}")
    return "\n".join(parts)


def equivalence_check_prompt() -> str:
    """Build the prompt for the equivalence-check stage. Pure code-review:
    the agent reads the original `src/lib.rs` (input to stage 2) and the
    Hax-rewritten one (output of stage 2), reasons about whether the rewrite
    preserved behavior, and ends with a VERDICT marker."""
    original_source = read_file(RUST_CRATE / "src" / "lib.rs")
    rewritten_source = read_file(WORKING_CRATE / "src" / "lib.rs")
    return f"""{PROMPT_ASSETS.equivalence_check_skill}

---

**Original `src/lib.rs`** (input to the rewrite stage, at `{RUST_CRATE}`):

```rust
{original_source}
```

**Hax-rewritten `src/lib.rs`** (output of the rewrite stage, at `{WORKING_CRATE}`):

```rust
{rewritten_source}
```

Read both, reason about whether the rewrite preserved runtime behavior, and end your response with a single line: `VERDICT: PASS` or `VERDICT: FAIL`.
"""


def select_examples_prompt() -> str:
    extraction_dir = WORKING_CRATE / "proofs" / "lean" / "extraction"
    target_extracted = render_extraction_files(extraction_dir)
    target_source = read_file(WORKING_CRATE / "src" / "lib.rs")
    manifests = render_examples_manifests()
    return f"""{PROMPT_ASSETS.select_examples_skill}

Target crate's extracted Lean files (under verification):
{target_extracted}

Target crate's src/lib.rs:
{target_source}

Library manifests (these are all `proof_patterns/*/manifest.json` in the project):
{manifests}

Pick up to 5 examples whose proof obstacles match the target's. Output paths as `proof_patterns/<name>` (one per line is easiest to parse) followed by your rationale, gaps, and rejections per the skill.

You may use Read with absolute paths under `{PROOF_PATTERNS_DIR}/<name>/` to inspect any candidate's source / obligations more deeply, but do not Read every example — only the promising ones from manifest tags.
"""


def make_lean_proof_prompt() -> str:
    extraction_dir = WORKING_CRATE / "proofs" / "lean" / "extraction"
    extracted_lean = render_extraction_files(extraction_dir)
    working_source = read_file(WORKING_CRATE / "src" / "lib.rs")
    obligations_notes = STAGE_NOTES.get("make_lean_obligations", "").strip()
    selector_notes = STAGE_NOTES.get("select_examples", "").strip()
    selected_paths = render_selected_example_paths(selector_notes) if selector_notes else ""

    notes_section = (
        f"""

Notes from the obligations stage (the agent that wrote the theorem statements):
The previous agent already explored the Hax prelude and may have suggested concrete proof tactics. Use this as a starting point — try the suggested tactics first before exploring the prelude from scratch.

{obligations_notes}
"""
        if obligations_notes
        else ""
    )
    if selected_paths:
        examples_section = f"""

Reference examples — closed-proof obligations files from past targets that the selection stage flagged as structurally similar. **Read at least the first one before attempting any tactic.** Their proof shapes are likely transferable; copying the pattern is almost always faster than rediscovering it from Hax prelude internals.

{selected_paths}

Selector's rationale (why these were picked, what each example covers, gaps in the library):

{selector_notes}
"""
    elif selector_notes:
        examples_section = f"""

Selector's notes (no obligations files were inlined — selector found no usable matches):

{selector_notes}
"""
    else:
        examples_section = ""
    return f"""{PROMPT_ASSETS.lean_proof_skill}
{_documentation_section()}{examples_section}
Working src/lib.rs (Rust source under verification):
{working_source}

Current Lean files in proofs/lean/extraction/ (extracted module + obligations companion):
{extracted_lean}{notes_section}"""


SYSTEM_PROMPT = """You are working in a Rust crate. Each pipeline stage runs in a fresh session — do not assume tool calls or file reads from previous stages are remembered.

You have three kinds of tools:

**Built-in inspection and orchestration tools** — use freely:
- `Read` — read any file
- `Grep` — search file contents (regex)
- `Glob` — find files by pattern
- `Bash` — run arbitrary shell commands for inspection (`find`, `wc`, `head`, ad-hoc Python `python3 -c ...`, etc.). Use for things the structured MCP runners don't cover.
- `TodoWrite` — track multi-step work as a checklist. Useful when a task layers several lemmas or files; write the plan as todos and mark each one as you finish so you don't lose the thread mid-turn.
- `Agent` / `Task` — spawn a sub-agent for broad exploration (e.g. scanning the Hax prelude for a specific lemma name, or surveying patterns across `proof_patterns/`). Cheaper than doing a long Grep+Read loop yourself when the search is wide.

**MCP tools** (prefixed with `mcp__pipeline__`) — use for state-changing operations on the working crate. These are logged for the pipeline's audit trail:
- `mcp__pipeline__write_working_file` — create or overwrite a file
- `mcp__pipeline__apply_file_patch_tool` — apply SEARCH/REPLACE patches to an existing file
- `mcp__pipeline__run_cargo_test`, `mcp__pipeline__run_cargo_hax_into_lean`, `mcp__pipeline__run_lake_build` — fixed external-command runners

Built-in `Write`, `Edit`, and `MultiEdit` are **not available** — they would bypass the harness's stage-specific path restriction (e.g. the proof stage may only edit `*Obligations.lean`). Use the MCP equivalents (`mcp__pipeline__write_working_file` / `mcp__pipeline__apply_file_patch_tool`) which enforce the restriction.

When using `apply_file_patch_tool`, the `patch` parameter uses SEARCH/REPLACE blocks:

<<< SEARCH
old text exactly as it appears in the file
===
new text
>>> REPLACE

You may include multiple SEARCH/REPLACE blocks in a single `patch` value. Each SEARCH block must match text that currently exists in the file. Always pass a non-empty `error_message` describing the concrete error or check output that motivated the patch."""

DISALLOWED_BUILTIN_TOOLS = [
    "Write",
    "Edit",
    "MultiEdit",
    "BashOutput",
    "KillShell",
    "WebFetch",
    "WebSearch",
    "ExitPlanMode",
    "NotebookEdit",
    "ToolSearch",
]


def _build_agent_options(
    short_tool_names: list[str], lean_lsp: bool = False
) -> ClaudeAgentOptions:
    """Assemble the ClaudeAgentOptions for an agent run — MCP servers, the
    allow-list, and the Lean LSP server when requested. Factored out of
    `run_agent` so a multi-turn caller (`make_proof`) can build options once
    and keep a single `ClaudeSDKClient` open across turns."""
    server = create_sdk_mcp_server(
        name=MCP_SERVER_NAME,
        version="1.0.0",
        tools=ALL_TOOLS,
    )

    mcp_servers: dict[str, Any] = {MCP_SERVER_NAME: server}
    allowed = [mcp_tool_name(n) for n in short_tool_names]

    if lean_lsp:
        # The Lean project root is the obligations lake project — the same dir
        # `run_lake_build` builds in. lean-lsp-mcp spawns `lake serve` there
        # and pushes diagnostics/goals incrementally (no `lake build` needed).
        lean_project = WORKING_CRATE / "proofs" / "lean" / "extraction"
        mcp_servers["lean"] = {
            "type": "stdio",
            "command": LEAN_LSP_MCP_COMMAND,
            "args": [
                *LEAN_LSP_MCP_BASE_ARGS,
                "--lean-project-path", str(lean_project),
                "--disable-tools", ",".join(LEAN_LSP_DISABLED_TOOLS),
            ],
            # Reuse the pipeline's curated env so the spawned `lake serve`
            # finds elan/lake on PATH, exactly like run_lake_build.
            "env": TOOL_ENV,
        }
        allowed += [f"mcp__lean__{t}" for t in LEAN_LSP_TOOLS]

    return ClaudeAgentOptions(
        model=MODEL_NAME,
        cwd=str(CURRENT_CRATE),
        mcp_servers=mcp_servers,
        allowed_tools=allowed,
        disallowed_tools=DISALLOWED_BUILTIN_TOOLS,
        permission_mode=PERMISSION_MODE,
        setting_sources=[],
        system_prompt=SYSTEM_PROMPT,
    )


async def _drain_response(client: ClaudeSDKClient) -> str:
    """Consume one query's worth of messages from an open client, echoing text
    and tool calls to stdout. Returns that turn's concatenated assistant text.
    Safe to call repeatedly on the same client — once per `client.query(...)`."""
    text_parts: list[str] = []
    async for message in client.receive_response():
        if isinstance(message, AssistantMessage):
            for block in message.content:
                if isinstance(block, TextBlock):
                    text_parts.append(block.text)
                    print(block.text, flush=True)
                elif isinstance(block, ToolUseBlock):
                    short_name = block.name.removeprefix(f"mcp__{MCP_SERVER_NAME}__")
                    inp_str = json.dumps(block.input) if isinstance(block.input, dict) else str(block.input)
                    print(f"[tool] {short_name}({_truncate(inp_str)})", flush=True)
        elif isinstance(message, ResultMessage):
            if message.result and message.result not in text_parts:
                text_parts.append(message.result)
                print(message.result, flush=True)
    return "\n".join(text_parts).strip()


async def run_agent(
    *, prompt: str, short_tool_names: list[str], lean_lsp: bool = False
) -> str:
    """Single-turn agent run: open a session, send one prompt, return its text."""
    options = _build_agent_options(short_tool_names, lean_lsp)
    async with ClaudeSDKClient(options=options) as client:
        await client.query(prompt)
        return await _drain_response(client)


async def make_pbt() -> int:
    global CURRENT_CRATE
    CURRENT_CRATE = RUST_CRATE

    STAGE_NOTES["make_pbt"] = await run_agent(
        prompt=make_pbt_prompt(),
        short_tool_names=[
            "write_working_file",
            "apply_file_patch_tool",
            "run_cargo_test",
        ],
    )
    return _verify_stage_postconditions(
        "make_pbt",
        [(["cargo", "test"], RUST_CRATE, "cargo test")],
    )


async def rust_hax_lean() -> int:
    global CURRENT_CRATE
    copy_rust_crate()
    CURRENT_CRATE = WORKING_CRATE

    STAGE_NOTES["rust_hax_lean"] = await run_agent(
        prompt=rewrite_to_lean_prompt(),
        short_tool_names=[
            "write_working_file",
            "apply_file_patch_tool",
            "run_cargo_test",
            "run_cargo_hax_into_lean",
            "run_lake_build",
        ],
    )
    extraction = WORKING_CRATE / "proofs" / "lean" / "extraction"
    return _verify_stage_postconditions(
        "rust_hax_lean",
        [
            (["cargo", "test"], WORKING_CRATE, "cargo test"),
            (["cargo", "hax", "into", "lean"], WORKING_CRATE, "cargo hax into lean"),
            (["lake", "build"], extraction, "lake build"),
        ],
    )


def harvest_rewrite_patterns_prompt() -> str:
    skill_text = HARVEST_REWRITE_PATTERNS_SKILL.read_text(encoding="utf-8")
    log_dir = RUST_CRATE / "attempted_changes" / RUN_TIMESTAMP
    existing = sorted(REWRITE_PATTERNS_DIR.glob("*.rs")) if REWRITE_PATTERNS_DIR.exists() else []
    existing_list = "\n".join(f"  - rewrite_patterns/{p.name}" for p in existing) or "  (none yet)"
    return f"""{skill_text}

---

This run's attempt log:
  {log_dir}

Look inside for subdirectories named `*_stage2_rust_hax_lean_*/`. Those are
the rewrite agent's patches. Ignore other stages.

Existing patterns to avoid duplicating:
{existing_list}

The archive lives at: {REWRITE_PATTERNS_DIR}
"""


async def harvest_rewrite_patterns() -> int:
    global CURRENT_CRATE
    CURRENT_CRATE = WORKING_CRATE

    STAGE_NOTES["harvest_rewrite_patterns"] = await run_agent(
        prompt=harvest_rewrite_patterns_prompt(),
        short_tool_names=["write_rewrite_pattern"],
    )
    return 0


async def make_lean_obligations() -> int:
    global CURRENT_CRATE
    CURRENT_CRATE = WORKING_CRATE

    prepare_obligations_scaffold(WORKING_CRATE)

    STAGE_NOTES["make_lean_obligations"] = await run_agent(
        prompt=make_lean_obligations_prompt(),
        short_tool_names=[
            "apply_file_patch_tool",
            "run_lake_build",
        ],
        lean_lsp=True,
    )
    extraction = WORKING_CRATE / "proofs" / "lean" / "extraction"
    result = _verify_stage_postconditions(
        "make_lean_obligations",
        [(["lake", "build"], extraction, "lake build")],
    )
    if result == 0:
        # Snapshot the public obligations now that the file is known to
        # build cleanly. The proof stage's preservation check compares
        # against this — see _verify_obligations_preserved. The disk copy
        # at `.obligations_snapshot.lean` is what --proof-only restores from.
        oblig = find_obligations_file_in(extraction)
        _snapshot_obligations(oblig)
        if oblig and oblig.is_file():
            shutil.copy2(oblig, oblig.parent / ".obligations_snapshot.lean")
    return result


_VERDICT_PATTERN = re.compile(r"VERDICT:\s*(PASS|FAIL)\b", re.IGNORECASE)


def parse_verdict(agent_output: str) -> str:
    """Find the last VERDICT marker in the agent's output. If absent, treat
    as FAIL (defensive default — a missing verdict means the agent didn't
    actually complete the equivalence check, so halt rather than silently
    proceed)."""
    matches = _VERDICT_PATTERN.findall(agent_output)
    if not matches:
        return "FAIL"
    return matches[-1].upper()


async def equivalence_check() -> int:
    """LLM code review: original src/lib.rs vs Hax-rewritten src/lib.rs.

    Read-only — the agent only inspects the two source files and returns a
    verdict (PASS / FAIL). The pipeline halts on FAIL; continues on PASS.
    A missing/unparseable verdict defaults to FAIL (see parse_verdict)."""
    global CURRENT_CRATE
    CURRENT_CRATE = WORKING_CRATE

    notes = await run_agent(
        prompt=equivalence_check_prompt(),
        short_tool_names=[],  # read-only — built-in Read/Grep/Glob only
    )
    STAGE_NOTES["equivalence_check"] = notes

    verdict = parse_verdict(notes)
    print(f"\n[equivalence_check] verdict: {verdict}")
    if verdict == "FAIL":
        print(f"[equivalence_check] halting pipeline — rewrite likely changed behavior")
        return 1
    return 0


async def select_examples() -> int:
    global CURRENT_CRATE
    CURRENT_CRATE = WORKING_CRATE

    STAGE_NOTES["select_examples"] = await run_agent(
        prompt=select_examples_prompt(),
        short_tool_names=[],  # read-only — built-in Read/Grep/Glob only
    )
    return 0


# Proof-stage retry policy: each turn opens a FRESH agent session.  Across the
# claude-opus-4-7 benchmark history, zero same-session continuations ever closed
# a file after an intermediate patch landed defeatist postmortem comments in it
# (the agent reads its own prior excuses and anchors on the same failed
# strategy).  We therefore start cold per retry and run a tiny `cleaner` agent
# between turns to scrub prior-attempt postmortems from the obligations file
# so the next session isn't biased by them.  MAX_PROOF_RETRIES extra attempts
# after the initial → MAX_PROOF_RETRIES + 1 turns total.
MAX_PROOF_RETRIES = 1


def _make_proof_cleaner_prompt() -> str:
    """The simplest possible cleanup-agent prompt: a janitor that strips
    prior-attempt postmortem comments and nothing else."""
    return (
        "You are a cleanup janitor running between proof-stage attempts.\n\n"
        "The obligations file at `proofs/lean/extraction/<...>Obligations.lean` "
        "still has surviving `sorry`s.  The previous agent likely editorialized "
        "in docstrings or block comments about why it could not close them.  "
        "Those postmortems anchor the next agent on the same failed strategy, "
        "so we strip them before retrying in a fresh session.\n\n"
        "REMOVE (via `apply_file_patch_tool` SEARCH/REPLACE patches) any "
        "comment or docstring prose that:\n"
        "  - says \"I tried\", \"could not\", \"couldn't\", \"gave up\", \"stuck\"\n"
        "  - cites \"session budget\", \"per-turn budget\", \"out of time\", \"in time\"\n"
        "  - describes what the prior agent attempted and failed at\n"
        "  - speculates about \"a different invariant\", \"future iteration would need\"\n"
        "  - has section headers like \"(broken)\" or \"STATUS:\" admissions of stuckness\n\n"
        "KEEP everything else, including:\n"
        "  - The theorem/lemma contract docstrings (the *what* of each obligation)\n"
        "  - Model-behavior diagnostics (e.g. \"`f(0) = RustM.fail`\", "
        "\"extracted body is `pure sorry`\", \"`sorryAx` is opaque\")\n"
        "  - All Lean code: imports, `def`, `theorem`, `lemma`, proofs, every `sorry` itself\n\n"
        "You are a janitor, not a prover.  Do NOT write tactics.  Do NOT edit "
        "theorem statements.  Do NOT remove any `sorry`.  Touch ONLY "
        "editorializing prose in docstrings and comments.  If the file has no "
        "such editorializing, exit without changes."
    )


async def _run_proof_cleaner() -> None:
    """Invoke the cleanup janitor agent between proof-stage turns.  Fire-and-forget:
    any failure here is non-fatal (worst case the next session reads an
    un-cleaned file, which is just the prior behaviour)."""
    try:
        await run_agent(
            prompt=_make_proof_cleaner_prompt(),
            short_tool_names=["apply_file_patch_tool"],
            lean_lsp=False,
        )
    except Exception as exc:
        print(f"[make_proof] cleaner failed (continuing anyway): {exc}")


async def make_proof() -> int:
    """Run the proof agent in a sequence of *fresh* sessions.

    Turn 1 is the initial attempt.  After the agent hands control back, while
    `sorry`s remain the pipeline runs a tiny `cleaner` agent over the
    obligations file (to strip any postmortem comments the previous turn
    landed) and then opens a NEW agent session for the next attempt — up to
    MAX_PROOF_RETRIES extra turns.

    Why fresh sessions: across the benchmark history, zero same-session
    continuations ever closed a file after an intermediate patch landed
    defeatist postmortem comments in it — the agent reads its own prior
    excuses and anchors on the same failed strategy.  A cold-started session
    over a scrubbed file empirically does close some cases that a
    same-session continuation does not (see sort_third).

    Stop conditions (whichever fires first):
    - 0 sorries remaining (success)
    - all turns used (hard ceiling on budget)"""
    global CURRENT_CRATE
    CURRENT_CRATE = WORKING_CRATE

    extraction_dir = WORKING_CRATE / "proofs" / "lean" / "extraction"
    total_turns = MAX_PROOF_RETRIES + 1
    parts: list[str] = []
    history: list[int] = []  # sorry count after each turn
    final_sorries = _count_real_sorries(find_obligations_file_in(extraction_dir))
    stop_reason = ""

    for turn in range(1, total_turns + 1):
        print(f"\n[make_proof] turn {turn}/{total_turns}")
        if turn > 1:
            print(f"[make_proof] running cleaner before turn {turn}")
            await _run_proof_cleaner()
        notes = await run_agent(
            prompt=make_lean_proof_prompt(),
            short_tool_names=[
                "write_working_file",
                "apply_file_patch_tool",
                "run_lake_build",
            ],
            lean_lsp=True,
        )

        oblig = find_obligations_file_in(extraction_dir)
        prior_sorries = history[-1] if history else None
        final_sorries = _count_real_sorries(oblig)
        history.append(final_sorries)
        delta_str = "" if prior_sorries is None else f" (was {prior_sorries})"
        parts.append(
            f"=== Turn {turn}/{total_turns} "
            f"({final_sorries} sorry remaining outside comments{delta_str}) ===\n{notes}"
        )
        print(f"[make_proof] turn {turn} done — {final_sorries} sorry remain{delta_str}")

        if final_sorries == 0:
            stop_reason = f"closed after {turn} turn(s)"
            print(f"[make_proof] {stop_reason}")
            break

    if not stop_reason:
        stop_reason = f"used all {total_turns} turns with {final_sorries} sorry remaining"
        print(f"[make_proof] {stop_reason}")

    turns_used = len(parts)
    header = (
        f"Final state after {turns_used}/{total_turns} turn(s): "
        f"{final_sorries} sorry remaining outside comments. "
        f"Stop reason: {stop_reason}. "
        f"Sorry trajectory: {history}.\n\n"
    )
    STAGE_NOTES["make_proof"] = header + "\n\n".join(parts)
    extraction = WORKING_CRATE / "proofs" / "lean" / "extraction"
    build_rc = _verify_stage_postconditions(
        "make_proof",
        [(["lake", "build"], extraction, "lake build")],
    )
    # Preservation is a soundness gate: even if the build passed, the proof
    # stage is forbidden from deleting or weakening any obligation that the
    # obligations stage produced. A preservation violation halts the run
    # ahead of any build-success report.
    preserve_rc = _verify_obligations_preserved(find_obligations_file_in(extraction))
    return preserve_rc or build_rc


def _strip_lean_comments(text: str) -> str:
    """Remove `/- ... -/` blocks and `-- ...` line comments. Good enough for
    the sorry-eligibility check; doesn't handle Lean's rare nested block
    comments, which the obligations files we produce don't use."""
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    text = re.sub(r"--[^\n]*", "", text)
    return text


def _count_real_sorries(oblig_path: Path | None) -> int:
    """Number of `sorry` keywords outside comments. Returns -1 if the file
    is missing — the caller treats that as 'not closed'."""
    if oblig_path is None or not oblig_path.exists():
        return -1
    body = _strip_lean_comments(oblig_path.read_text(encoding="utf-8"))
    return len(re.findall(r"\bsorry\b", body))


def _obligations_is_closed(oblig_path: Path | None) -> bool:
    return _count_real_sorries(oblig_path) == 0


def _obligations_has_theorems(oblig_path: Path | None) -> bool:
    """True iff the file exists and contains at least one `theorem`, `lemma`,
    or `example` declaration outside comments. The bare scaffold has imports
    and an `end <namespace>` line but no declarations — that returns False."""
    if oblig_path is None or not oblig_path.exists():
        return False
    body = _strip_lean_comments(oblig_path.read_text(encoding="utf-8"))
    return re.search(r"^\s*(theorem|lemma|example)\b", body, re.MULTILINE) is not None


# Top-level `theorem <name>` declarations. The `^theorem` anchor (with
# MULTILINE) excludes `private theorem` / `protected theorem` — those start
# with a different keyword, so they don't match — meaning helpers the proof
# agent introduces are correctly ignored. An optional `@[…]` attribute line
# directly above is permitted. Captures the name and the signature text up
# to `:=`; the proof body is not captured (only the statement is checked).
_OBLIGATION_DECL_PATTERN = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*\n[ \t]*)?theorem[ \t]+([A-Za-z_][\w']*)([\s\S]*?):=",
    re.MULTILINE,
)


def _extract_obligations(text: str) -> dict[str, str]:
    """Map each public obligation's name to its normalized statement.

    Comments are stripped first so the boilerplate header can't interfere.
    Each top-level `theorem <name>` (excluding `private`/`protected` — those
    are scaffolding the proof agent may freely add or remove) yields one
    entry whose value is the text between the name and `:=`, with whitespace
    runs collapsed so trivial reflow doesn't register as a change."""
    stripped = _strip_lean_comments(text)
    out: dict[str, str] = {}
    for m in _OBLIGATION_DECL_PATTERN.finditer(stripped):
        out[m.group(1)] = " ".join(m.group(2).split())
    return out


def _snapshot_obligations(oblig_path: Path | None) -> None:
    """Record the public obligations at the end of the obligations stage,
    so the proof stage's preservation check has something to compare
    against. Only called once `lake build` has confirmed the file is
    well-typed (otherwise the snapshot would capture an inconsistent
    state)."""
    global _OBLIGATIONS_SNAPSHOT
    if oblig_path is None or not oblig_path.is_file():
        _OBLIGATIONS_SNAPSHOT = None
        return
    _OBLIGATIONS_SNAPSHOT = _extract_obligations(
        oblig_path.read_text(encoding="utf-8")
    )
    print(
        f"[make_lean_obligations] snapshotted {len(_OBLIGATIONS_SNAPSHOT)} "
        "obligation(s) for the proof-stage preservation check"
    )


def _verify_obligations_preserved(oblig_path: Path | None) -> int:
    """Compare the current obligations file against the snapshot taken at
    the end of the obligations stage. The proof agent is permitted to
    *close* obligations (replace a `sorry` body with a real proof) but
    never to delete or weaken them. Returns 0 if every snapshotted
    obligation still exists with an unchanged statement, 1 otherwise.
    Adding new obligations, and adding/removing `private` helpers, is
    allowed — neither narrows the public contract."""
    if _OBLIGATIONS_SNAPSHOT is None:
        return 0  # nothing was snapshotted — nothing to compare against
    if oblig_path is None or not oblig_path.is_file():
        print(
            "[obligation-preservation] obligations file is missing — the "
            "proof stage appears to have removed it. Halting.",
            file=sys.stderr,
        )
        return 1
    current = _extract_obligations(oblig_path.read_text(encoding="utf-8"))
    deleted: list[str] = []
    modified: list[tuple[str, str, str]] = []
    for name, before in _OBLIGATIONS_SNAPSHOT.items():
        if name not in current:
            deleted.append(name)
        elif current[name] != before:
            modified.append((name, before, current[name]))
    if not deleted and not modified:
        return 0
    print(
        "\n[obligation-preservation] the proof stage altered the public contract:",
        file=sys.stderr,
    )
    for name in deleted:
        print(f"  deleted:  theorem {name}", file=sys.stderr)
    for name, before, after in modified:
        print(f"  modified: theorem {name}", file=sys.stderr)
        print(f"    before: {before[:200]}{'…' if len(before) > 200 else ''}", file=sys.stderr)
        print(f"    after:  {after[:200]}{'…' if len(after) > 200 else ''}", file=sys.stderr)
    print(
        "\n  The proof agent may only close obligations, not delete or weaken "
        "them. Halting pipeline.",
        file=sys.stderr,
    )
    return 1


def harvest_proof_patterns_prompt() -> str:
    skill_text = HARVEST_PROOF_PATTERNS_SKILL.read_text(encoding="utf-8")
    oblig_path = find_obligations_file_in(WORKING_CRATE / "proofs" / "lean" / "extraction")
    oblig_content = oblig_path.read_text(encoding="utf-8") if oblig_path else "(missing)"
    src_path = WORKING_CRATE / "src" / "lib.rs"
    src_content = src_path.read_text(encoding="utf-8") if src_path.exists() else "(missing)"
    manifests = render_examples_manifests()
    default_name = WORKING_CRATE.name
    return f"""{skill_text}

---

**Working crate**: `{WORKING_CRATE}`
**Default `name` argument for `add_proof_pattern`**: `{default_name}` (use this unless you have a specific structural reason to override).

**Target `src/lib.rs`**:

```rust
{src_content}
```

**Target obligations file** (`{oblig_path.name if oblig_path else "missing"}`):

```
{oblig_content}
```

**Existing library entries** (manifests):

{manifests}

Decide: add (call `add_proof_pattern`) or skip (don't call anything). End with one sentence: `ADDED <name>` or `SKIPPED — covered by <existing entry>`.
"""


async def harvest_proof_patterns() -> int:
    global CURRENT_CRATE
    CURRENT_CRATE = WORKING_CRATE

    oblig_path = find_obligations_file_in(WORKING_CRATE / "proofs" / "lean" / "extraction")
    if not _obligations_has_theorems(oblig_path):
        msg = "(skipped: obligations file missing or contains no theorems — nothing to harvest)"
        STAGE_NOTES["harvest_proof_patterns"] = msg
        print(f"[harvest_proof_patterns] {msg}")
        return 0
    if not _obligations_is_closed(oblig_path):
        msg = "(skipped: obligations file still contains `sorry` outside comments)"
        STAGE_NOTES["harvest_proof_patterns"] = msg
        print(f"[harvest_proof_patterns] {msg}")
        return 0

    STAGE_NOTES["harvest_proof_patterns"] = await run_agent(
        prompt=harvest_proof_patterns_prompt(),
        short_tool_names=["add_proof_pattern"],
    )
    return 0


def _kill_orphan_lean_lsp_processes() -> None:
    """Best-effort cleanup of orphan Lean LSP processes from prior runs.

    The `lean-lsp-mcp` stdio MCP server (spawned per-stage when `lean_lsp=True`)
    forks `lake serve`, which forks `lean --server`, which forks `lean --worker`
    instances per open file. When the agent's `ClaudeSDKClient` session ends,
    only the immediate MCP child gets `SIGTERM` — its descendants are not in
    its process group and become orphans reparented to PID 1.

    Those orphans keep file handles on `.lake/packages/` and sometimes
    actively write there (cache updates, lockfile refreshes, `.DS_Store`).
    That makes `rust_hax_lean`'s `rm -rf $WORKING_CRATE` race-fail with
    `Directory not empty`, halting the pipeline before stage 2 even starts.

    This runs at the top of every pipeline invocation as a stopgap. The real
    fix is to put each MCP server's command in its own process group at spawn
    time and `killpg` the group when the agent session ends. That requires
    threading through `claude_agent_sdk`, so for now we just pre-kill.

    Caveat: if another pipeline run is concurrently using these processes,
    this will kill them too. Don't run two pipelines on the same machine
    simultaneously."""
    patterns = [
        "lake serve.*extraction",
        "lean --server.*extraction",
        "lean --worker.*Obligations",
        "lean-lsp-mcp",
    ]
    killed = 0
    for pat in patterns:
        result = subprocess.run(["pkill", "-f", pat], check=False, capture_output=True)
        if result.returncode == 0:
            killed += 1
    if killed:
        print(f"[cleanup] Killed orphan Lean LSP processes "
              f"({killed}/{len(patterns)} patterns matched).")


async def main() -> int:
    global RUN_TIMESTAMP, ATTEMPT_LOG_DIR, ATTEMPT_COUNTER, CURRENT_STAGE, CURRENT_CRATE, MODE_SUFFIX

    RUN_TIMESTAMP = datetime.now().strftime("%Y%m%d-%H%M%S")
    ATTEMPT_LOG_DIR = None
    ATTEMPT_COUNTER = 0
    STAGE_NOTES.clear()
    if PROOF_ONLY:
        MODE_SUFFIX = "_proof_only_continue" if PROOF_ONLY_CONTINUE else "_proof_only"

    runs_dir = ROOT / "runs"
    runs_dir.mkdir(parents=True, exist_ok=True)
    log_path = runs_dir / f"{RUN_TIMESTAMP}_{CRATE_NAME}{MODE_SUFFIX}.log"
    log_file = open(log_path, "w", encoding="utf-8")
    sys.stdout = Tee(sys.__stdout__, log_file)
    sys.stderr = Tee(sys.__stderr__, log_file)

    print(f"Log: {log_path}")
    print(f"Model: {MODEL_NAME}")
    _kill_orphan_lean_lsp_processes()

    if PROOF_ONLY:
        extraction = WORKING_CRATE / "proofs" / "lean" / "extraction"
        oblig = find_obligations_file_in(extraction)
        if oblig is None:
            print(f"--proof-only: no obligations file under {extraction}. "
                  f"Run the full pipeline on this crate once first.", file=sys.stderr)
            return 2
        snapshot = extraction / ".obligations_snapshot.lean"
        stages_desc = "make_proof" + (" + harvest_proof_patterns" if HARVEST_ENABLED else "")
        if PROOF_ONLY_CONTINUE:
            print(f"Stages: {stages_desc} (--continue: using current obligations file as-is)")
        else:
            if not snapshot.is_file():
                print(f"--proof-only: no obligations snapshot at {snapshot}. "
                      f"Run the full pipeline once first to capture one, "
                      f"or use --continue to proceed against the current file.",
                      file=sys.stderr)
                return 2
            shutil.copy2(snapshot, oblig)
            print(f"Stages: {stages_desc} (--proof-only: obligations restored from snapshot)")
        _snapshot_obligations(oblig)
        CURRENT_CRATE = WORKING_CRATE
        stages: list[tuple[str, Any]] = [("make_proof", make_proof)]
        if HARVEST_ENABLED:
            stages.append(("harvest_proof_patterns", harvest_proof_patterns))
    else:
        print(f"Attempt logs: {RUST_CRATE / 'attempted_changes' / RUN_TIMESTAMP}")
        if HARVEST_ENABLED:
            print("Stages: all 8 (1-8), in order")
        else:
            print("Stages: 6 (harvest stages disabled via --no-harvest; libraries frozen)")

        ensure_crate_setup()

        stages = [
            ("make_pbt", make_pbt),
            ("rust_hax_lean", rust_hax_lean),
        ]
        if HARVEST_ENABLED:
            stages.append(("harvest_rewrite_patterns", harvest_rewrite_patterns))
        stages += [
            ("equivalence_check", equivalence_check),
            ("select_examples", select_examples),
            ("make_lean_obligations", make_lean_obligations),
            ("make_proof", make_proof),
        ]
        if HARVEST_ENABLED:
            stages.append(("harvest_proof_patterns", harvest_proof_patterns))

    for stage_name, stage in stages:
        CURRENT_STAGE = stage_name
        result = await stage()
        if result != 0:
            print(f"Stage failed: {stage_name} (exit code {result})")
            _record_incomplete_stage(stage_name, result)
            _persist_stage_notes(runs_dir)
            return result
        print("")
        print(stage_name)

    _persist_stage_notes(runs_dir)
    _clear_incomplete_stage()
    cleanup_build_artifacts(WORKING_CRATE)
    return 0


def _persist_stage_notes(runs_dir: Path) -> None:
    if not STAGE_NOTES:
        return
    notes_path = runs_dir / f"{RUN_TIMESTAMP}_{CRATE_NAME}{MODE_SUFFIX}_stage_notes.json"
    notes_path.write_text(json.dumps(STAGE_NOTES, indent=2), encoding="utf-8")
    print(f"Stage notes: {notes_path}")


def _record_incomplete_stage(stage_name: str, exit_code: int) -> None:
    """Write incomplete_stages/<crate>.json naming the stage that halted the
    pipeline. One file per crate, overwritten each failing run — a flat
    overview of which crates are stuck and where."""
    INCOMPLETE_STAGES_DIR.mkdir(parents=True, exist_ok=True)
    path = INCOMPLETE_STAGES_DIR / f"{CRATE_NAME}.json"
    payload = {
        "crate": CRATE_NAME,
        "failed_stage": stage_name,
        "exit_code": exit_code,
        "timestamp": RUN_TIMESTAMP,
        "log": str(ROOT / "runs" / f"{RUN_TIMESTAMP}_{CRATE_NAME}{MODE_SUFFIX}.log"),
    }
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"Incomplete stage recorded: {path}")


def _clear_incomplete_stage() -> None:
    """Drop a stale incomplete_stages/<crate>.json after a fully successful
    run, so the folder only ever lists crates that are currently failing."""
    path = INCOMPLETE_STAGES_DIR / f"{CRATE_NAME}.json"
    if path.exists():
        path.unlink()
        print(f"Cleared prior incomplete-stage record: {path}")


def _dir_size(path: Path) -> int:
    total = 0
    for entry in path.rglob("*"):
        try:
            if entry.is_file() and not entry.is_symlink():
                total += entry.stat().st_size
        except OSError:
            pass
    return total


def _human_bytes(n: float) -> str:
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n:.1f}{unit}"
        n /= 1024
    return f"{n:.1f}TB"


def cleanup_build_artifacts(crate_dir: Path) -> None:
    """Strip large regenerable build artifacts from the working crate.
    Cargo and Lake recreate these on demand; deleting them keeps the
    benchmarks tree small (`target/` is typically 100-500MB per crate,
    `.lake/` 50-200MB). Source, Cargo.toml/Cargo.lock, and proof files
    are left intact."""
    targets = [
        crate_dir / "target",
        crate_dir / "proofs" / "lean" / "extraction" / ".lake",
        crate_dir / "proofs" / "lean" / "extraction" / "lake-manifest.json",
    ]
    freed = 0
    for path in targets:
        if not path.exists():
            continue
        try:
            size = _dir_size(path) if path.is_dir() else path.stat().st_size
        except OSError:
            size = 0
        try:
            subprocess.run(["rm", "-rf", str(path)], check=True)
            freed += size
        except subprocess.CalledProcessError as exc:
            print(f"[cleanup] failed to remove {path}: {exc}", file=sys.stderr)
    if freed > 0:
        try:
            shown = crate_dir.relative_to(ROOT)
        except ValueError:
            shown = crate_dir
        print(f"[cleanup] freed {_human_bytes(freed)} from {shown}")


if __name__ == "__main__":
    raise SystemExit(asyncio.run(main()))
