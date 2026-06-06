"""Faithful probe: spawn an agent with the SAME access as the pipeline's
obligations/prover stages (run_agent(..., lean_lsp=True)) and have it report
whether the mcp__lean__* tools are actually available."""
import asyncio
import os
import sys

sys.path.insert(0, "/home/tobias/uni/pipeline_v6")
os.chdir("/home/tobias/uni/pipeline_v6")

# pipeline.py parses sys.argv and reads RUST_CRATE/src/lib.rs at import time.
sys.argv = ["pipeline.py", "benchmarks/code/alloc/is_size_align_valid_usize"]

import pipeline  # noqa: E402

# Mirror the obligations stage exactly: it sets CURRENT_CRATE = WORKING_CRATE
pipeline.CURRENT_CRATE = pipeline.WORKING_CRATE

PROBE = """\
You are a diagnostic probe. Do EXACTLY this, nothing else:

1. State which tools whose names start with mcp__lean__ you have available
   (list them, or say "NONE").
2. If any exist, call mcp__lean__lean_file_outline with file_path
   "Is_size_align_valid_usizeObligations.lean" and report verbatim whether the
   call returned an outline or errored.
3. End your reply with one line exactly:
   PROBE_RESULT: LEAN_MCP_AVAILABLE   (if step 2 succeeded)
   PROBE_RESULT: LEAN_MCP_UNAVAILABLE (if no mcp__lean__ tools, or the call failed)

Do not edit files. Do not call run_lake_build. Be terse.
"""


async def main() -> None:
    print(f"[probe] WORKING_CRATE   = {pipeline.WORKING_CRATE}")
    print(f"[probe] lean project    = "
          f"{pipeline.WORKING_CRATE / 'proofs' / 'lean' / 'extraction'}")
    print(f"[probe] model           = {pipeline.MODEL_NAME}")
    print(f"[probe] permission_mode = {pipeline.PERMISSION_MODE}")
    print(f"[probe] lean-lsp-mcp    = uvx lean-lsp-mcp@{pipeline.LEAN_LSP_MCP_VERSION}")
    print("[probe] launching agent with lean_lsp=True ...\n" + "=" * 60)
    out = await pipeline.run_agent(
        prompt=PROBE,
        short_tool_names=["run_lake_build"],  # same non-lean tool set shape
        lean_lsp=True,                        # <-- the obligations/prover wiring
    )
    print("=" * 60 + "\n[probe] agent final text:\n" + out)


asyncio.run(main())