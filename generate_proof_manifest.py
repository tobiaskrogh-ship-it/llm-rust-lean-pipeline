"""Populate <example-path>/manifest.json by running the manifest-generation skill."""

import asyncio
import json
import os
import re
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
PROOF_PATTERNS_DIR = ROOT / "proof_patterns"
SKILL_FILE = ROOT / "skills" / "generate_example_manifest.md"

USAGE = """\
Usage: python generate_proof_manifest.py <example-path>

  <example-path>   Path to a closed-proof crate (e.g. proof_patterns/add_one).

Reads the closed-proof crate at <example-path>/ and overwrites its
manifest.json with feature tags + summary.
"""


def parse_args(argv: list[str]) -> str:
    if len(argv) != 2:
        print(USAGE, file=sys.stderr)
        sys.exit(2)
    if argv[1] in ("-h", "--help"):
        print(USAGE)
        sys.exit(0)
    return argv[1]


_EXAMPLE_INPUT = parse_args(sys.argv)
EXAMPLE_DIR = Path(_EXAMPLE_INPUT).resolve()
if not EXAMPLE_DIR.is_dir():
    print(f"Example not found: {_EXAMPLE_INPUT}", file=sys.stderr)
    sys.exit(2)
try:
    EXAMPLE_DIR.relative_to(PROOF_PATTERNS_DIR)
except ValueError:
    print(
        f"Wrong folder: '{_EXAMPLE_INPUT}'. "
        f"generate_proof_manifest.py only operates on entries under proof_patterns/. "
        f"Use: python generate_proof_manifest.py proof_patterns/<name>",
        file=sys.stderr,
    )
    sys.exit(2)

MODEL_NAME = os.getenv("CLAUDE_MODEL", "claude-opus-4-7")
PERMISSION_MODE = os.getenv("CLAUDE_PERMISSION_MODE", "bypassPermissions")
MCP_SERVER_NAME = "generate_proof_manifest"


def safe_path(rel_path: str) -> Path:
    rel = Path(rel_path)
    if rel.is_absolute():
        raise ValueError(f"Absolute paths are not allowed: {rel_path}")
    resolved = (EXAMPLE_DIR / rel).resolve()
    root = EXAMPLE_DIR.resolve()
    try:
        resolved.relative_to(root)
    except ValueError as exc:
        raise ValueError(f"Path escapes example: {rel_path}") from exc
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


@tool(
    "apply_file_patch_tool",
    "Apply a SEARCH/REPLACE patch to a file in the example directory.",
    {
        "type": "object",
        "properties": {
            "path": {"type": "string", "description": "Path relative to the example directory"},
            "patch": {"type": "string", "description": "SEARCH/REPLACE patch blocks"},
        },
        "required": ["path", "patch"],
    },
)
async def apply_file_patch_tool_tool(args: dict[str, Any]) -> dict[str, Any]:
    try:
        resolved = safe_path(args["path"])
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
    "write_working_file",
    "Create or overwrite a file in the example directory.",
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
        resolved = safe_path(args["path"])
        overwrite = bool(args.get("overwrite", False))
        if resolved.exists() and not overwrite:
            return _mcp_text(f"ERROR: {args['path']} exists; pass overwrite=true")
        resolved.parent.mkdir(parents=True, exist_ok=True)
        resolved.write_text(args["content"], encoding="utf-8")
        return _mcp_text(f"OK: wrote {args['path']}")
    except Exception as exc:
        return _mcp_text(f"ERROR: {exc}")


SYSTEM_PROMPT = f"""You are populating an example library entry's manifest.json.

You have:
- Built-in `Read`, `Grep`, `Glob` for inspection.
- `mcp__{MCP_SERVER_NAME}__apply_file_patch_tool` for SEARCH/REPLACE edits to manifest.json.
- `mcp__{MCP_SERVER_NAME}__write_working_file` if the manifest does not exist.

Built-in `Write`, `Edit`, `MultiEdit`, and `Bash` are NOT available. Use the MCP equivalents.

Patch format:

<<< SEARCH
old text exactly as it appears in the file
===
new text
>>> REPLACE

Multiple SEARCH/REPLACE blocks may appear in one `patch` value.
"""

DISALLOWED_BUILTIN_TOOLS = [
    "Write", "Edit", "MultiEdit", "Bash", "BashOutput", "KillShell",
    "Agent", "Task", "WebFetch", "WebSearch", "TodoWrite",
    "ExitPlanMode", "NotebookEdit", "ToolSearch",
]


def _load_other_manifests() -> list[tuple[Path, dict[str, Any]]]:
    """Parsed manifests from every example except the one being populated."""
    out: list[tuple[Path, dict[str, Any]]] = []
    for path in sorted(PROOF_PATTERNS_DIR.glob("*/manifest.json")):
        if path.parent == EXAMPLE_DIR:
            continue
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue
        if isinstance(data, dict):
            out.append((path, data))
    return out


def _tag_frequency_table(manifests: list[tuple[Path, dict[str, Any]]]) -> str:
    """Compute per-tag coverage across the library and classify each tag.

    WEAK     >= 40% of entries — broad-coverage; treat as filler unless this
                                  entry's single defining feature.
    STANDARD 1 <= count < 40%   — normal obstacle vocabulary; reuse when it fits.
    (FRESH tags don't appear in this table by definition; the agent coins them
    when no existing tag carries the right meaning.)
    """
    if not manifests:
        return "(no other manifests yet — first entry; tag vocabulary is whatever you set here)"
    n = len(manifests)
    weak_threshold = 0.40
    counts: dict[str, int] = {}
    for _, data in manifests:
        feats = data.get("features", []) if isinstance(data, dict) else []
        if not isinstance(feats, list):
            continue
        for tag in feats:
            if isinstance(tag, str):
                counts[tag] = counts.get(tag, 0) + 1
    if not counts:
        return "(other manifests exist but contain no feature tags)"
    weak: list[tuple[str, int]] = []
    standard: list[tuple[str, int]] = []
    for tag, c in counts.items():
        (weak if c / n >= weak_threshold else standard).append((tag, c))
    weak.sort(key=lambda x: (-x[1], x[0]))
    standard.sort(key=lambda x: (-x[1], x[0]))
    lines = [f"Library size: {n} other manifest(s). Threshold for WEAK: tag on >= {int(weak_threshold * 100)}% of entries.\n"]
    if weak:
        lines.append("WEAK tags (broad coverage — at most one in your final set, and only if literally the defining feature):")
        for tag, c in weak:
            lines.append(f"  - {tag}  ({c}/{n} = {c / n:.0%})")
    else:
        lines.append("WEAK tags: (none)")
    lines.append("")
    if standard:
        lines.append("STANDARD tags (existing vocabulary — reuse when an existing tag fits the obstacle precisely):")
        for tag, c in standard:
            lines.append(f"  - {tag}  ({c}/{n})")
    else:
        lines.append("STANDARD tags: (none yet)")
    lines.append("")
    lines.append(
        "FRESH tags are anything not on either list above. Coin a fresh tag when no existing one\n"
        "carries the meaning you need — especially for transferable proof techniques (Tier-1 tags),\n"
        "which by their nature often haven't been named yet."
    )
    return "\n".join(lines)


def _render_existing_manifests(manifests: list[tuple[Path, dict[str, Any]]]) -> str:
    if not manifests:
        return "(no other manifests yet)"
    parts = []
    for path, _ in manifests:
        try:
            parts.append(f"=== {path.relative_to(ROOT)} ===\n{path.read_text(encoding='utf-8')}")
        except OSError:
            continue
    return "\n\n".join(parts) if parts else "(no other manifests yet)"


def build_prompt() -> str:
    skill_text = SKILL_FILE.read_text(encoding="utf-8")
    try:
        display_path = str(EXAMPLE_DIR.relative_to(ROOT))
    except ValueError:
        display_path = str(EXAMPLE_DIR)
    manifests = _load_other_manifests()
    return f"""{skill_text}

================================================================
Tag-frequency table for the current library
================================================================
{_tag_frequency_table(manifests)}

================================================================
Full existing manifests (for context — read these to see how
similar entries phrased their obstacles, but don't blindly copy
weak vocabulary)
================================================================
{_render_existing_manifests(manifests)}

================================================================
Working directory: `{display_path}/`
================================================================
Inspect, in this order:
1. `proofs/lean/extraction/*Obligations.lean` — closed proofs. Ground truth for what was proved and what techniques the proof used.
2. `proofs/lean/extraction/*.lean` — the extracted module. Function shape after Hax.
3. `src/lib.rs` — Rust source. Context only; don't tag from this alone.

Verify no `sorry` / `axiom` / `native_decide` in the obligations file before tagging.

Produce the reasoning trace from the skill (transferable moves, tag candidates, rejected candidates, final set, summary), THEN call `apply_file_patch_tool` to overwrite `manifest.json`.
"""


async def run() -> int:
    server = create_sdk_mcp_server(
        name=MCP_SERVER_NAME,
        version="1.0.0",
        tools=[apply_file_patch_tool_tool, write_working_file_tool],
    )
    options = ClaudeAgentOptions(
        model=MODEL_NAME,
        cwd=str(EXAMPLE_DIR),
        mcp_servers={MCP_SERVER_NAME: server},
        allowed_tools=[
            f"mcp__{MCP_SERVER_NAME}__apply_file_patch_tool",
            f"mcp__{MCP_SERVER_NAME}__write_working_file",
        ],
        disallowed_tools=DISALLOWED_BUILTIN_TOOLS,
        permission_mode=PERMISSION_MODE,
        setting_sources=[],
        system_prompt=SYSTEM_PROMPT,
    )

    print(f"Example: {EXAMPLE_DIR}")
    print(f"Model: {MODEL_NAME}")

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
                        inp = json.dumps(block.input) if isinstance(block.input, dict) else str(block.input)
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

    return 0


if __name__ == "__main__":
    raise SystemExit(asyncio.run(run()))
