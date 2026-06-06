"""Portable Lean-LSP-MCP probe for THIS machine — semantic test.

Verifies not just that the mcp__lean__* tools connect, but that the server
is operating against a real, built Lean environment: it points the agent at
`proof_patterns/recursion_example` (a closed-proof crate whose extraction dir
has a populated .lake — the extracted module + the Hax-prelude oleans) and
has the agent call the *semantic* tools (diagnostics + goal state). A closed
proof file that elaborates clean proves the LSP genuinely loaded the Lean
environment, not just parsed syntax.

Leaves the Linux-targeted probe_lean_lsp.py untouched.
"""
import asyncio
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
# Any valid benchmarks/code crate — only needed so `import pipeline` succeeds
# (pipeline.py reads RUST_CRATE/src/lib.rs at import time).
IMPORT_CRATE = "benchmarks/code/starting_examples/square"
# The actual Lean project the LSP server is pointed at: a built, closed proof.
LEAN_CRATE = ROOT / "proof_patterns" / "recursion_example"
OBLIGATIONS = "Recursion_exampleObligations.lean"

sys.path.insert(0, str(ROOT))
os.chdir(ROOT)
sys.argv = ["pipeline.py", IMPORT_CRATE]

import pipeline  # noqa: E402

# run_agent derives the lean project as WORKING_CRATE/proofs/lean/extraction
# and uses CURRENT_CRATE as the agent cwd. Point both at the built crate.
pipeline.WORKING_CRATE = LEAN_CRATE
pipeline.CURRENT_CRATE = LEAN_CRATE / "proofs" / "lean" / "extraction"

PROBE = f"""\
You are a diagnostic probe. The Lean project you are pointed at is a fully
built, closed-proof crate. Do EXACTLY this, nothing else:

1. Call mcp__lean__lean_diagnostic_messages on file_path "{OBLIGATIONS}".
   Report verbatim what came back — the diagnostics list, or that there were
   none, or any error text.
2. Read "{OBLIGATIONS}", pick a line/column inside a tactic proof (a line
   after a ':= by'), and call mcp__lean__lean_goal at that position. Report
   verbatim whether a goal state (or "no goals") came back, or an error.
3. End your reply with exactly one line:
   PROBE_RESULT: LEAN_ENV_WORKING  -- if step 1 returned real elaboration
       output (an empty / clean diagnostic list counts: it means the file
       elaborated successfully against the Hax prelude)
   PROBE_RESULT: LEAN_ENV_BROKEN   -- if step 1 shows the environment failed
       to load (e.g. unknown module / import errors for Hax or Std)

Be terse. Do not edit files. Do not call run_lake_build.
"""


async def main() -> None:
    ext = pipeline.WORKING_CRATE / "proofs" / "lean" / "extraction"
    print(f"[probe] ROOT            = {ROOT}")
    print(f"[probe] lean project    = {ext}")
    print(f"[probe] .lake present   = {(ext / '.lake').is_dir()}")
    print(f"[probe] model           = {pipeline.MODEL_NAME}")
    print(f"[probe] lean-lsp-mcp    = uvx lean-lsp-mcp@{pipeline.LEAN_LSP_MCP_VERSION}")
    print("[probe] launching agent with lean_lsp=True ...\n" + "=" * 60)
    out = await pipeline.run_agent(
        prompt=PROBE,
        short_tool_names=["run_lake_build"],
        lean_lsp=True,
    )
    print("=" * 60 + "\n[probe] agent final text:\n" + out)


asyncio.run(main())
