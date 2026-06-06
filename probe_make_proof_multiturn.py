"""Focused test of the multi-turn make_proof session.

`make_proof` was changed to keep ONE `ClaudeSDKClient` open and send several
`query()` turns into it ("keep going" nudges) instead of cold-restarting a
fresh agent per attempt. This probe exercises exactly that mechanism, using the
pipeline's own `_build_agent_options` / `_drain_response`, by running 3 turns in
one open session and checking that context from turn 1 survives into turns 2-3.

It deliberately does NOT run the full pipeline: testing_crate is `add(l,r)=l+r`,
whose proof closes in turn 1, so a full run would never reach the continuation
turns. This probe forces all 3 turns regardless.
"""
import asyncio
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
# pipeline.py parses sys.argv at import time and needs a real crate under
# benchmarks/code/. Hand it one; we only use the module's helper functions.
sys.argv = ["pipeline.py", str(ROOT / "benchmarks/code/starting_examples/add_one")]

import pipeline  # noqa: E402

from claude_agent_sdk import ClaudeSDKClient  # noqa: E402

TURNS = [
    "Remember this secret token: ZEBRA-7. Reply with exactly the word OK and nothing else.",
    "What was the secret token I gave you? Reply with exactly the token, nothing else.",
    "Append the digits 99 to that token. Reply with exactly the result, nothing else.",
]


async def main() -> int:
    options = pipeline._build_agent_options(short_tool_names=[], lean_lsp=False)
    replies: list[str] = []

    async with ClaudeSDKClient(options=options) as client:
        for i, prompt in enumerate(TURNS, start=1):
            print(f"\n--- turn {i}/{len(TURNS)} -> query ---")
            print(f"  prompt: {prompt}")
            await client.query(prompt)
            reply = await pipeline._drain_response(client)
            replies.append(reply)
            print(f"  reply : {reply!r}")

    # Turns 2 and 3 can only answer if the open session preserved turn 1's
    # context — i.e. the multi-turn loop make_proof relies on works.
    ok2 = "ZEBRA-7" in replies[1]
    ok3 = "ZEBRA-7" in replies[2] and "99" in replies[2]
    print("\n=== verdict ===")
    print(f"  turn 2 recalled turn-1 context : {'PASS' if ok2 else 'FAIL'}")
    print(f"  turn 3 built on turn-1 context : {'PASS' if ok3 else 'FAIL'}")
    if ok2 and ok3:
        print("  RESULT: PASS - one open session carried context across 3 turns")
        return 0
    print("  RESULT: FAIL - context did not survive across turns")
    return 1


if __name__ == "__main__":
    raise SystemExit(asyncio.run(main()))
