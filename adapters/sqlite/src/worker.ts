import { SqliteD1Adapter } from "./adapter"

export interface Env {
  DB: D1Database
}

type D1Database = {
  prepare (sql: string): any
  batch<T = unknown> (stmts: any[]): Promise<any[]>
  exec (sql: string): Promise<any>
}

export default {
  async fetch (req: Request, env: Env): Promise<Response> {
    const url = new URL(req.url)
    const adapter = new SqliteD1Adapter(env.DB)

    if (url.pathname === "/_caps") {
      return Response.json(adapter.caps)
    }

    return new Response("runtime not wired yet", { status: 501 })
  },
}
