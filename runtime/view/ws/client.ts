// /runtime/view/ws/client.ts

export type SubCallback = (event: any) => void

export class CicscRealtimeClient {
  private ws: WebSocket | null = null
  private subscriptions = new Map<string, { params: any, callback: SubCallback }>()
  private reconnectTimeout = 1000
  private maxReconnectTimeout = 30000

  constructor(
    private url: string, // e.g. wss://api.cicsc.dev/ws
    private tenantId: string,
    private token: string
  ) { }

  connect () {
    const wsUrl = new URL(this.url)
    wsUrl.searchParams.set("tenant_id", this.tenantId)
    wsUrl.searchParams.set("token", this.token)

    this.ws = new WebSocket(wsUrl.toString())

    this.ws.onopen = () => {
      this.reconnectTimeout = 1000
      // Re-subscribe to existing on reconnect
      for (const [subId, { params }] of this.subscriptions.entries()) {
        this.send({ type: "subscribe", subscriptionId: subId, params })
      }
    }

    this.ws.onmessage = (evt) => {
      try {
        const data = JSON.parse(evt.data)
        if (data.type === "event") {
          const sub = this.subscriptions.get(data.subscriptionId)
          if (sub) sub.callback(data.payload)
        }
      } catch (e) {
        // ignore malformed
      }
    }

    this.ws.onclose = () => {
      setTimeout(() => {
        this.reconnectTimeout = Math.min(this.reconnectTimeout * 2, this.maxReconnectTimeout)
        this.connect()
      }, this.reconnectTimeout)
    }
  }

  subscribe (subscriptionId: string, params: any, callback: SubCallback) {
    this.subscriptions.set(subscriptionId, { params, callback })
    if (this.ws?.readyState === 1 /* WebSocket.OPEN */) {
      this.send({ type: "subscribe", subscriptionId, params })
    }
  }

  unsubscribe (subscriptionId: string) {
    this.subscriptions.delete(subscriptionId)
    if (this.ws?.readyState === 1 /* WebSocket.OPEN */) {
      this.send({ type: "unsubscribe", subscriptionId })
    }
  }

  private send (msg: any) {
    this.ws?.send(JSON.stringify(msg))
  }
}
