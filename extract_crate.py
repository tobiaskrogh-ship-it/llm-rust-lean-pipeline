"""Extract every tractable function from a scope inside a Rust source crate
in `to_be_extracted/<crate>/` into self-contained benchmark crates.

The CLI arg may be a crate root, a subdirectory, or a single file. The
script walks up to find Cargo.toml (for source metadata) and passes the
original path to the agent as the *scope* it should explore.

The destination parent is `benchmarks/code/<scope-name>/`, where
`<scope-name>` is the directory name or file stem of the scope. (All
source benchmarks live under `benchmarks/code/`; the per-model `_modified`
working copies that pipeline.py creates live under `benchmarks/<MODEL_NAME>/`.)
Each child crate that gets re-extracted overwrites any previous version;
there is no skip-if-exists check.

One LLM driver per scope. The driver explores, decides what to extract,
scaffolds each child crate with `cargo new`, fills it in, and verifies
with `cargo test`. No upfront regex enumeration — the LLM finds
extractable functionality wherever it lives (free fns, impl methods,
methods inside macro_rules definitions, etc.).

Usage:
  python extract_crate.py <path>

Examples:
  python extract_crate.py to_be_extracted/num-integer-0.1.46
  # writes: benchmarks/code/num-integer-0.1.46/<fn>_<type>/

  python extract_crate.py to_be_extracted/core-1.94.0/src/alloc
  # writes: benchmarks/code/alloc/<fn>_<type>/

  python extract_crate.py to_be_extracted/core-1.94.0/src/bool.rs
  # writes: benchmarks/code/bool/<fn>_<type>/
"""

import asyncio
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

from claude_agent_sdk import (
    AssistantMessage,
    ClaudeAgentOptions,
    ClaudeSDKClient,
    ResultMessage,
    TextBlock,
    ToolResultBlock,
    ToolUseBlock,
    UserMessage,
    create_sdk_mcp_server,
    tool,
)

ROOT = Path(__file__).resolve().parent
BENCHMARKS_DIR = ROOT / "benchmarks" / "code"
SKILL_FILE = ROOT / "skills" / "extract_concrete_implementation.md"

USAGE = """\
Usage: python extract_crate.py <path>

  <path>   A crate root, a subdirectory, or a single .rs file inside
           to_be_extracted/. Examples:
             to_be_extracted/num-integer-0.1.46         -> benchmarks/code/num-integer-0.1.46/
             to_be_extracted/core-1.94.0/src/alloc      -> benchmarks/code/alloc/
             to_be_extracted/core-1.94.0/src/bool.rs    -> benchmarks/code/bool/

The destination parent is benchmarks/code/<scope-name>/, where <scope-name>
is the directory name or file stem of the scope path. The script also walks
up to find Cargo.toml so source metadata (crate name, version) can still
be recorded in each extracted child's [package.metadata.extracted_from].
"""


def parse_args(argv: list[str]) -> str:
    if any(arg in ("-h", "--help") for arg in argv[1:]):
        print(USAGE)
        sys.exit(0)
    if len(argv) != 2:
        print(USAGE, file=sys.stderr)
        sys.exit(2)
    return argv[1]


def find_crate_root(p: Path) -> Path | None:
    cur = p if p.is_dir() else p.parent
    while True:
        if (cur / "Cargo.toml").is_file():
            return cur
        if cur == cur.parent:
            return None
        cur = cur.parent


SCOPE_PATH_ARG = parse_args(sys.argv)
SCOPE_PATH = (ROOT / SCOPE_PATH_ARG).resolve()

if not SCOPE_PATH.exists():
    print(f"Path not found: {SCOPE_PATH}", file=sys.stderr)
    sys.exit(2)

SOURCE_CRATE = find_crate_root(SCOPE_PATH)
if SOURCE_CRATE is None:
    print(f"No Cargo.toml found at or above {SCOPE_PATH}", file=sys.stderr)
    sys.exit(2)

SCOPE_NAME = SCOPE_PATH.name if SCOPE_PATH.is_dir() else SCOPE_PATH.stem
DEST_PARENT = BENCHMARKS_DIR / SCOPE_NAME
DEST_PARENT.mkdir(parents=True, exist_ok=True)

MODEL_NAME = os.getenv("CLAUDE_MODEL", "claude-opus-4-7")
PERMISSION_MODE = os.getenv("CLAUDE_PERMISSION_MODE", "bypassPermissions")
MCP_SERVER_NAME = "extract_crate"

DISALLOWED_BUILTIN_TOOLS = [
    "Write", "Edit", "MultiEdit", "Bash", "BashOutput", "KillShell",
    "Agent", "Task", "WebFetch", "WebSearch", "TodoWrite",
    "ExitPlanMode", "NotebookEdit", "ToolSearch",
]

TOOL_ENV = os.environ.copy()
HOME = Path.home()
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


def parse_source_metadata(source_crate: Path) -> dict[str, str]:
    cargo_path = source_crate / "Cargo.toml"
    if not cargo_path.exists():
        return {}
    text = cargo_path.read_text(encoding="utf-8")
    name = re.search(r'^name\s*=\s*"([^"]+)"', text, flags=re.MULTILINE)
    version = re.search(r'^version\s*=\s*"([^"]+)"', text, flags=re.MULTILINE)
    return {
        "name": name.group(1) if name else source_crate.name,
        "version": version.group(1) if version else "0.0.0",
    }


SOURCE_META = parse_source_metadata(SOURCE_CRATE)


_VALID_CRATE_NAME = re.compile(r"^[a-z][a-z0-9_]*$")


def safe_path_in(rel_path: str, root: Path) -> Path:
    rel = Path(rel_path)
    if rel.is_absolute():
        raise ValueError(f"Absolute paths are not allowed: {rel_path}")
    resolved = (root / rel).resolve()
    root_resolved = root.resolve()
    try:
        resolved.relative_to(root_resolved)
    except ValueError as exc:
        raise ValueError(f"Path escapes destination root: {rel_path}") from exc
    return resolved


def apply_patch_to_text(original: str, patch: str) -> str:
    pattern = re.compile(
        r"<<< SEARCH\r?\n(.*?)\r?\n===\r?\n(.*?)\r?\n>>> REPLACE",
        re.DOTALL,
    )
    if not patch.strip():
        raise ValueError("Patch is empty")
    matches = list(pattern.finditer(patch))
    if not matches:
        raise ValueError(
            "No SEARCH/REPLACE blocks found. Use:\n"
            "<<< SEARCH\nold\n===\nnew\n>>> REPLACE"
        )
    updated = original
    for idx, m in enumerate(matches, start=1):
        search, replace = m.group(1), m.group(2)
        if search not in updated:
            raise ValueError(f"Search block {idx} not found:\n{search}")
        updated = updated.replace(search, replace, 1)
    return updated


def _mcp_text(text: str) -> dict[str, Any]:
    return {"content": [{"type": "text", "text": text}]}


def make_mcp_tools(dest_parent: Path):
    @tool(
        "cargo_init_crate",
        "Scaffold a new Cargo library crate at <destination>/<crate_name>/. "
        "Runs `cargo new --vcs none --lib --edition 2024`. Returns the relative path.",
        {
            "type": "object",
            "properties": {
                "crate_name": {
                    "type": "string",
                    "description": "Snake-case name (e.g. 'isqrt_u64').",
                },
            },
            "required": ["crate_name"],
        },
    )
    async def cargo_init_crate_tool(args: dict[str, Any]) -> dict[str, Any]:
        try:
            name = args["crate_name"]
            if not _VALID_CRATE_NAME.match(name):
                return _mcp_text(
                    f"ERROR: crate name must match [a-z][a-z0-9_]*: {name!r}"
                )
            dest = dest_parent / name
            if dest.exists():
                shutil.rmtree(dest, ignore_errors=True)
            result = subprocess.run(
                ["cargo", "new", "--vcs", "none", "--lib",
                 "--edition", "2024", str(dest)],
                env=TOOL_ENV,
                capture_output=True,
                text=True,
                timeout=60,
            )
            if result.returncode != 0:
                if dest.exists():
                    shutil.rmtree(dest, ignore_errors=True)
                return _mcp_text(f"ERROR: cargo new failed:\n{result.stderr}")
            return _mcp_text(f"OK: created {dest.relative_to(ROOT)}")
        except Exception as exc:
            return _mcp_text(f"ERROR: {exc}")

    @tool(
        "write_working_file",
        "Create or overwrite a file under the destination folder. "
        "Path is relative to that folder (e.g. 'isqrt_u64/src/lib.rs').",
        {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "content": {"type": "string"},
                "overwrite": {"type": "boolean", "default": False},
            },
            "required": ["path", "content"],
        },
    )
    async def write_working_file_tool(args: dict[str, Any]) -> dict[str, Any]:
        try:
            resolved = safe_path_in(args["path"], dest_parent)
            overwrite = bool(args.get("overwrite", False))
            if resolved.exists() and not overwrite:
                return _mcp_text(f"ERROR: {args['path']} exists; pass overwrite=true")
            resolved.parent.mkdir(parents=True, exist_ok=True)
            resolved.write_text(args["content"], encoding="utf-8")
            return _mcp_text(f"OK: wrote {args['path']}")
        except Exception as exc:
            return _mcp_text(f"ERROR: {exc}")

    @tool(
        "apply_file_patch_tool",
        "Apply a SEARCH/REPLACE patch to a file under the destination folder. "
        "Path is relative to that folder.",
        {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "patch": {"type": "string"},
            },
            "required": ["path", "patch"],
        },
    )
    async def apply_file_patch_tool_tool(args: dict[str, Any]) -> dict[str, Any]:
        try:
            resolved = safe_path_in(args["path"], dest_parent)
            original = resolved.read_text(encoding="utf-8") if resolved.exists() else ""
            updated = apply_patch_to_text(original, args["patch"])
            if updated == original:
                return _mcp_text(f"OK: no changes for {args['path']}")
            resolved.parent.mkdir(parents=True, exist_ok=True)
            resolved.write_text(updated, encoding="utf-8")
            return _mcp_text(f"OK: patched {args['path']}")
        except Exception as exc:
            return _mcp_text(f"ERROR: {exc}")

    @tool(
        "run_cargo_test",
        "Run `cargo test` inside a child crate at <destination>/<crate_name>/.",
        {
            "type": "object",
            "properties": {
                "crate_name": {"type": "string"},
            },
            "required": ["crate_name"],
        },
    )
    async def run_cargo_test_tool(args: dict[str, Any]) -> dict[str, Any]:
        try:
            name = args["crate_name"]
            crate_dir = dest_parent / name
            if not crate_dir.is_dir():
                return _mcp_text(f"ERROR: no such crate {name}")
            result = subprocess.run(
                ["cargo", "test"],
                cwd=str(crate_dir),
                env=TOOL_ENV,
                capture_output=True,
                text=True,
                timeout=180,
            )
            return _mcp_text(json.dumps({
                "ok": result.returncode == 0,
                "returncode": result.returncode,
                "stdout": result.stdout[-4000:],
                "stderr": result.stderr[-4000:],
            }))
        except Exception as exc:
            return _mcp_text(f"ERROR: {exc}")

    return [
        cargo_init_crate_tool,
        write_working_file_tool,
        apply_file_patch_tool_tool,
        run_cargo_test_tool,
    ]


SYSTEM_PROMPT = f"""You are extracting many functions from a Rust source crate into self-contained benchmark crates. You drive the entire process for one source crate in a single session.

Available tools:
- Built-in `Read`, `Grep`, `Glob` to inspect the source crate (read-only).
- `mcp__{MCP_SERVER_NAME}__cargo_init_crate` to scaffold a new child crate.
- `mcp__{MCP_SERVER_NAME}__write_working_file` to create/overwrite files inside any child crate.
- `mcp__{MCP_SERVER_NAME}__apply_file_patch_tool` for SEARCH/REPLACE edits.
- `mcp__{MCP_SERVER_NAME}__run_cargo_test` to verify a child crate.

Built-in `Write`, `Edit`, `MultiEdit`, and `Bash` are NOT available — use the MCP equivalents.

All `path` arguments to write/patch tools are RELATIVE to the destination folder (the prompt below names the exact path). For example, after `cargo_init_crate(crate_name="isqrt_u64")`, you write its lib at path `isqrt_u64/src/lib.rs`.

SEARCH/REPLACE patch format:

<<< SEARCH
old text exactly as it appears
===
new text
>>> REPLACE
"""


def build_prompt() -> str:
    skill_text = SKILL_FILE.read_text(encoding="utf-8")
    try:
        source_rel = SOURCE_CRATE.relative_to(ROOT)
    except ValueError:
        source_rel = SOURCE_CRATE
    try:
        scope_rel = SCOPE_PATH.relative_to(ROOT)
    except ValueError:
        scope_rel = SCOPE_PATH
    try:
        dest_rel = DEST_PARENT.relative_to(ROOT)
    except ValueError:
        dest_rel = DEST_PARENT

    scope_kind = "directory" if SCOPE_PATH.is_dir() else "single file"

    return f"""{skill_text}

---

This is one driver session. You will repeat the skill above MANY times — once per function you decide to extract.

- **Source crate**: `{source_rel}` (absolute: `{SOURCE_CRATE}`). Read-only — explore with built-in Read/Grep/Glob.
- **Source crate published name**: `{SOURCE_META.get('name', SOURCE_CRATE.name)}` (use in `[package.metadata.extracted_from] crate = "..."`)
- **Source crate version**: `{SOURCE_META.get('version', '0.0.0')}` (use in `[package.metadata.extracted_from] version = "..."`)
- **Scope** ({scope_kind}): `{scope_rel}`. **Only extract functions defined inside this scope.** Helpers/dependencies invoked from your scoped functions may live elsewhere in the crate — you may Read those to inline them, but do NOT extract them as separate child crates.
- **Destination folder**: `{dest_rel}/` (every child crate goes directly under here, flat)
- **Default monomorphization type**: `u64` for unsigned contexts, `i64` for signed. Encode the chosen type both in the crate name (`<fn>_u64`) and in `[package.metadata.extracted_from] type = "..."`.

Workflow per extraction:

1. Explore the source. Pick a function to extract.
2. Call `cargo_init_crate(crate_name="<fn>_<type>")`. This produces a default `Cargo.toml` and a placeholder `src/lib.rs`.
3. Overwrite the generated `Cargo.toml` (`write_working_file` with `overwrite=true`) so it matches the skill's required shape: `[package]` (name, version=0.1.0, edition=2024), then `[package.metadata.extracted_from]` with `crate`, `version`, `function`, `type`, `function_path` (plus `impl_type`/`impl_trait` if extracting from an impl). **No `[dependencies]` section.**
4. Overwrite `src/lib.rs` with the inlined function body, any private helpers it needs, and a `#[cfg(test)] mod tests` block with tests transferred verbatim from the source (monomorphized to the concrete type, call sites rewritten to the local function).
5. Call `run_cargo_test(crate_name="...")`. Iterate on the lib until it passes.
6. Move on to the next function.

Continue until you've extracted every tractable function. **Skip and note** (do not even create the crate):

- Anything that bottoms out in an intrinsic (`core::intrinsics::*`, `extern "rust-intrinsic"`).
- FFI / `extern "C"` bindings.
- `async` functions / anything requiring a runtime.
- Inline assembly (`asm!`).
- Functions whose only meaningful body is `unsafe` pointer arithmetic that can't be safely rewritten.
- Functions inside `macro_rules!` whose substitution is too complex to expand by hand.

**Begin by reporting your exploration plan**: a short survey of what extractable functions exist in this source, grouped roughly. Then start extracting. This gives the user a chance to sanity-check scope before you spend many tool calls.

At the end, output an aggregate summary: every crate created (pass/fail), every function deliberately skipped (one-line reason each).
"""


async def main() -> int:
    print(f"Source crate:  {SOURCE_CRATE}")
    print(f"Scope:         {SCOPE_PATH}  ({'dir' if SCOPE_PATH.is_dir() else 'file'})")
    print(f"Destination:   {DEST_PARENT}")
    print(f"Model:         {MODEL_NAME}")
    print()

    server = create_sdk_mcp_server(
        name=MCP_SERVER_NAME,
        version="1.0.0",
        tools=make_mcp_tools(DEST_PARENT),
    )
    options = ClaudeAgentOptions(
        model=MODEL_NAME,
        cwd=str(DEST_PARENT),
        mcp_servers={MCP_SERVER_NAME: server},
        allowed_tools=[
            f"mcp__{MCP_SERVER_NAME}__cargo_init_crate",
            f"mcp__{MCP_SERVER_NAME}__write_working_file",
            f"mcp__{MCP_SERVER_NAME}__apply_file_patch_tool",
            f"mcp__{MCP_SERVER_NAME}__run_cargo_test",
        ],
        disallowed_tools=DISALLOWED_BUILTIN_TOOLS,
        permission_mode=PERMISSION_MODE,
        setting_sources=[],
        system_prompt=SYSTEM_PROMPT,
    )

    def _truncate(s: str, limit: int = 200) -> str:
        s = s.replace("\n", "\\n")
        return s if len(s) <= limit else s[:limit] + f"... [+{len(s) - limit} chars]"

    async with ClaudeSDKClient(options=options) as client:
        await client.query(build_prompt())
        async for message in client.receive_response():
            if isinstance(message, AssistantMessage):
                for block in message.content:
                    if isinstance(block, TextBlock):
                        print(block.text, flush=True)
                    elif isinstance(block, ToolUseBlock):
                        short = block.name.removeprefix(f"mcp__{MCP_SERVER_NAME}__")
                        inp = (json.dumps(block.input) if isinstance(block.input, dict)
                               else str(block.input))
                        print(f"[tool] {short}({_truncate(inp)})", flush=True)
            elif isinstance(message, UserMessage):
                for block in message.content:
                    if isinstance(block, ToolResultBlock):
                        if isinstance(block.content, str):
                            text = block.content
                        elif isinstance(block.content, list):
                            text = "".join(
                                item.get("text", "") if isinstance(item, dict) else str(item)
                                for item in block.content
                            )
                        else:
                            text = str(block.content)
                        marker = "[tool error]" if block.is_error else "[tool result]"
                        print(f"{marker} {_truncate(text)}", flush=True)
            elif isinstance(message, ResultMessage):
                if message.result:
                    print(message.result, flush=True)

    print(f"\n{'=' * 60}")
    print("Final verification")
    print(f"{'=' * 60}")
    children = sorted(p for p in DEST_PARENT.iterdir() if p.is_dir())
    pass_count = fail_count = 0
    for child in children:
        if not (child / "src" / "lib.rs").exists() or not (child / "Cargo.toml").exists():
            continue
        result = subprocess.run(
            ["cargo", "test"],
            cwd=str(child),
            env=TOOL_ENV,
            capture_output=True,
            text=True,
            timeout=180,
        )
        ok = result.returncode == 0 and "test result: ok" in result.stdout
        symbol = "✓" if ok else "✗"
        rel = child.relative_to(ROOT)
        print(f"  {symbol}  {rel}")
        if ok:
            pass_count += 1
        else:
            fail_count += 1
    print()
    print(f"  pass: {pass_count}  /  fail: {fail_count}  /  total: {pass_count + fail_count}")
    return 0 if fail_count == 0 else 1


if __name__ == "__main__":
    raise SystemExit(asyncio.run(main()))
