// /runtime/view/ws/manager.ts

export type WSMessage =
  | { type: "subscribe"; subscriptionId: string; params?: Record<string, any> }
  | { type: "unsubscribe"; subscriptionId: string }
  | { type: "ping" }

export type WSEvent = {
  type: "event"
  subscriptionId: string
  payload: any
  seq?: number
}

export class ConnectionManager {
  private connections = new Set<{
    socket: WebSocket
    tenantId: string
    subscriptions: Map<string, any> // subId -> params
  }>()

  handleConnection (tenantId: string, socket: WebSocket) {
    const conn: any = {
      socket,
      tenantId,
      subscriptions: new Map<string, any>()
    }
    this.connections.add(conn)

    // @ts-ignore - Cloudflare Workers specific
    socket.accept()

    socket.addEventListener("message", (evt: any) => {
      try {
        const msg = JSON.parse(evt.data as string) as WSMessage
        this.onMessage(conn, msg)
      } catch (e) {
        socket.send(JSON.stringify({ type: "error", message: "Invalid JSON" }))
      }
    })

    socket.addEventListener("close", () => {
      this.connections.delete(conn)
    })

    socket.addEventListener("error", () => {
      this.connections.delete(conn)
    })
  }

  private onMessage (conn: any, msg: WSMessage) {
    switch (msg.type) {
      case "subscribe":
        conn.subscriptions.set(msg.subscriptionId, msg.params || {})
        conn.socket.send(JSON.stringify({ type: "subscribed", subscriptionId: msg.subscriptionId }))
        break
      case "unsubscribe":
        conn.subscriptions.delete(msg.subscriptionId)
        conn.socket.send(JSON.stringify({ type: "unsubscribed", subscriptionId: msg.subscriptionId }))
        break
      case "ping":
        conn.socket.send(JSON.stringify({ type: "pong" }))
        break
    }
  }

  broadcast (tenantId: string, subscriptionId: string, payload: any) {
    for (const conn of this.connections) {
      if (conn.tenantId !== tenantId) continue
      if (conn.subscriptions.has(subscriptionId)) {
        conn.socket.send(JSON.stringify({
          type: "event",
          subscriptionId: subscriptionId,
          payload: payload
        }))
      }
    }
  }
}

export const wsManager = new ConnectionManager()
