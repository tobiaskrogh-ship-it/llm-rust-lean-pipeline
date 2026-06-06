"""Direct MCP-stdio diagnostic for lean-lsp-mcp: spawn the exact server
command the pipeline uses, do the initialize + tools/list handshake, and
report timing / stderr — for two different --lean-project-path values, to
isolate whether a built .lake breaks startup."""
import json
import os
import select
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
sys.argv = ["pipeline.py", "benchmarks/code/starting_examples/square"]
import pipeline  # noqa: E402  — for LEAN_LSP_* constants + TOOL_ENV

PROJECTS = {
    "square (no .lake)": ROOT / "benchmarks/claude-opus-4-7/starting_examples/"
                                 "square_modified/proofs/lean/extraction",
    "recursion_example (built .lake)": ROOT / "proof_patterns/recursion_example/"
                                              "proofs/lean/extraction",
}


def run_one(label: str, project: Path) -> None:
    print(f"\n{'=' * 64}\n{label}\n  path: {project}\n  exists: {project.is_dir()}"
          f"  .lake: {(project / '.lake').is_dir()}\n{'=' * 64}")
    cmd = [
        "uvx", f"lean-lsp-mcp@{pipeline.LEAN_LSP_MCP_VERSION}",
        "--lean-project-path", str(project),
        "--disable-tools", ",".join(pipeline.LEAN_LSP_DISABLED_TOOLS),
    ]
    t0 = time.monotonic()
    proc = subprocess.Popen(
        cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, env=pipeline.TOOL_ENV, bufsize=1,
    )

    def send(obj: dict) -> None:
        proc.stdin.write(json.dumps(obj) + "\n")
        proc.stdin.flush()

    def read_line(timeout: float) -> str | None:
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            if proc.poll() is not None:
                return None
            r, _, _ = select.select([proc.stdout], [], [], 0.5)
            if r:
                return proc.stdout.readline()
        return None

    try:
        send({"jsonrpc": "2.0", "id": 1, "method": "initialize",
              "params": {"protocolVersion": "2025-06-18", "capabilities": {},
                         "clientInfo": {"name": "diag", "version": "0"}}})
        init = read_line(90)
        print(f"  [{time.monotonic()-t0:6.1f}s] initialize -> "
              f"{'OK' if init else 'NO RESPONSE'}")
        if not init:
            raise RuntimeError("no initialize response")
        send({"jsonrpc": "2.0", "method": "notifications/initialized"})
        send({"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}})
        tl = read_line(90)
        if tl:
            try:
                tools = json.loads(tl).get("result", {}).get("tools", [])
                names = sorted(t["name"] for t in tools)
                print(f"  [{time.monotonic()-t0:6.1f}s] tools/list -> "
                      f"{len(names)} tools: {names}")
            except Exception as exc:
                print(f"  tools/list parse error: {exc}\n  raw: {tl[:300]}")
        else:
            print(f"  [{time.monotonic()-t0:6.1f}s] tools/list -> NO RESPONSE")
    finally:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
        err = proc.stderr.read()
        if err.strip():
            print(f"  --- stderr ({len(err)} bytes) ---")
            for ln in err.strip().splitlines()[-25:]:
                print(f"  | {ln}")


for label, project in PROJECTS.items():
    run_one(label, project)
