import asyncio
from typing import Any

from claude_agent_sdk import (
    AssistantMessage,
    ClaudeAgentOptions,
    ClaudeSDKClient,
    ResultMessage,
    TextBlock,
    create_sdk_mcp_server,
    tool,
)


@tool(
    "ping",
    "Return the string 'pong'. Call this tool to verify tool use works.",
    {"type": "object", "properties": {}},
)
async def ping_tool(_: dict[str, Any]) -> dict[str, Any]:
    print("[smoke] ping tool was called")
    return {"content": [{"type": "text", "text": "pong"}]}


async def main() -> None:
    server = create_sdk_mcp_server(name="smoke", version="1.0.0", tools=[ping_tool])

    options = ClaudeAgentOptions(
        mcp_servers={"smoke": server},
        allowed_tools=["mcp__smoke__ping"],
        permission_mode="bypassPermissions",
        setting_sources=[],
        system_prompt="You must call the mcp__smoke__ping tool exactly once, then reply with the text it returned.",
    )

    print("[smoke] opening client...")
    async with ClaudeSDKClient(options=options) as client:
        await client.query("Call the ping tool and tell me what it returned.")

        async for message in client.receive_response():
            if isinstance(message, AssistantMessage):
                for block in message.content:
                    if isinstance(block, TextBlock):
                        print(f"[assistant] {block.text}")
            elif isinstance(message, ResultMessage):
                print(f"[result] subtype={message.subtype} cost=${message.total_cost_usd}")
                if message.result:
                    print(f"[result] {message.result}")


if __name__ == "__main__":
    asyncio.run(main())
