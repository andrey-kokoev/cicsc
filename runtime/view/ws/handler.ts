// /runtime/view/ws/handler.ts

import { wsManager } from "./manager"

export async function handleWebSocketUpgrade (req: Request, tenantId: string): Promise<Response> {
  const upgradeHeader = req.headers.get("Upgrade")
  if (!upgradeHeader || upgradeHeader !== "websocket") {
    return new Response("Expected Upgrade: websocket", { status: 426 })
  }

  const url = new URL(req.url)
  const token = url.searchParams.get("token")
  if (!token) {
    return new Response("Unauthorized: missing token", { status: 401 })
  }

  // @ts-ignore - Cloudflare Workers specific
  const [client, server] = new WebSocketPair()

  wsManager.handleConnection(tenantId, server)

  return new Response(null, {
    status: 101,
    webSocket: client,
  })
}
