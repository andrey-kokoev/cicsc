// /runtime/http/worker.ts

import { makeD1Store } from "../db/d1-store"
import { executeCommandTx } from "../execute-command-tx"
import type { VmIntrinsics } from "../../core/vm/eval"

import { SqliteD1Adapter } from "../../adapters/sqlite/src/adapter"
import type { CoreIrV0 } from "../../core/ir/types"
import { validateBundleV0 } from "../../core/ir/validate"
import { verifyHistoryAgainstIr } from "../../core/runtime/verify"
import { activateVersion } from "../db/activate-version"
import { putBundle } from "../db/bundle-registry"
import { compileSpecToBundleV0, readSpecBody } from "./compile"
import { loadTenantBundle } from "./tenant-bundle"

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
    try {
      const url = new URL(req.url)

      const adapter = new SqliteD1Adapter(env.DB as any)
      const store = makeD1Store({ adapter })

      // Intrinsics: wire your auth/roles here. v0: permissive defaults.
      const intrinsics: VmIntrinsics = {
        has_role: () => true,
        role_of: () => "user",
        auth_ok: () => true,
        constraint: () => true,
        len: (v: any) => (Array.isArray(v) ? v.length : typeof v === "string" ? v.length : v && typeof v === "object" ? Object.keys(v).length : 0),
        str: (v: any) => (v === null ? null : String(v)),
        int: (v: any) => (typeof v === "number" ? Math.trunc(v) : typeof v === "string" && v.trim() !== "" ? Number.parseInt(v, 10) : null),
        float: (v: any) => (typeof v === "number" ? v : typeof v === "string" && v.trim() !== "" ? Number.parseFloat(v) : null),
      }

      if (url.pathname === "/_caps") return Response.json(adapter.caps)

      // POST /install  (idempotent)
      if (url.pathname === "/install" && req.method === "POST") {
        const body = (await req.json().catch(() => ({}))) as any
        const tenant_id = String(body.tenant_id ?? "t")
        const loaded = await loadTenantBundle(env.DB as any, tenant_id)
        const ir = loaded.bundle.core_ir as CoreIrV0
        await activateVersion({
          db: env.DB as any,
          ir,
          version: loaded.active_version,
          tenant_id,
          setActiveVersion: store.setActiveVersion,
        })
        return Response.json({ ok: true })
      }

      // POST /compile  (returns bundle JSON; does not persist)
      if (url.pathname === "/compile" && req.method === "POST") {
        const body = await readSpecBody(req)
        const bundle = compileSpecToBundleV0(body)
        return Response.json({ ok: true, bundle })
      }

      // POST /bundle  (stores bundle, returns bundle_hash)
      if (url.pathname === "/bundle" && req.method === "POST") {
        const body = (await req.json().catch(() => ({}))) as any

        let bundle: any
        if (body && typeof body === "object" && body.core_ir && typeof body.core_ir === "object") {
          const v = validateBundleV0(body)
          if (!v.ok) return jsonErr(400, `invalid bundle: ${v.errors[0]?.path ?? "?"} ${v.errors[0]?.message ?? ""}`)
          bundle = v.value
        } else {
          bundle = compileSpecToBundleV0(body)
        }

        const out = await putBundle(env.DB as any, bundle)
        return Response.json({ ok: true, bundle_hash: out.bundle_hash })
      }

      // POST /install-from-spec  (compile + install schema; does not persist bundle)
      if (url.pathname === "/install-from-spec" && req.method === "POST") {
        const body = await readSpecBody(req)
        const bundle = compileSpecToBundleV0(body)
        const irV = bundle.core_ir as CoreIrV0

        const jsonBody = typeof body === "string" ? null : body
        const tenant_id =
          jsonBody && typeof jsonBody === "object" && (jsonBody as any).tenant_id
            ? String((jsonBody as any).tenant_id)
            : url.searchParams.get("tenant_id") ?? "t"

        await activateVersion({
          db: env.DB as any,
          ir: irV,
          version: 0,
          tenant_id,
          setActiveVersion: store.setActiveVersion,
        })
        return Response.json({ ok: true })
      }

      // POST /cmd/:type/:name
      const cmdMatch = url.pathname.match(/^\/cmd\/([^\/]+)\/([^\/]+)$/)
      if (cmdMatch && req.method === "POST") {
        const entity_type = decodeURIComponent(cmdMatch[1]!)
        const command_name = decodeURIComponent(cmdMatch[2]!)

        const body = (await req.json().catch(() => ({}))) as any
        const tenant_id = String(body.tenant_id ?? "t")
        const actor_id = String(body.actor_id ?? "u")
        const command_id = String(body.command_id ?? crypto.randomUUID())
        const entity_id = String(body.entity_id ?? crypto.randomUUID())
        const input = (body.input ?? {}) as any
        const dedupe_window_seconds =
          body.dedupe_window_seconds == null ? undefined : Number(body.dedupe_window_seconds)

        const now = Math.floor(Date.now() / 1000)
        const loaded = await loadTenantBundle(env.DB as any, tenant_id)
        const ir = loaded.bundle.core_ir as CoreIrV0

        const result = await executeCommandTx({
          ir,
          store: { adapter: store.adapter }, // store created by makeD1Store; has adapter on it
          intrinsics,
          req: {
            tenant_id,
            actor_id,
            command_id,
            entity_type,
            entity_id,
            command_name,
            input,
            now,
            dedupe_window_seconds:
              dedupe_window_seconds != null && Number.isFinite(dedupe_window_seconds)
                ? dedupe_window_seconds
                : undefined,
            // example: allow constraint args in request body
            constraint_args: body.constraint_args ?? {},
          },
        })

        return Response.json({ ok: true, result })
      }

      // GET /view/:name?tenant_id=...  (args via query string later)
      const viewMatch = url.pathname.match(/^\/view\/([^\/]+)$/)
      if (viewMatch && req.method === "GET") {
        const view_name = decodeURIComponent(viewMatch[1]!)
        const tenant_id = url.searchParams.get("tenant_id") ?? "t"
        const loaded = await loadTenantBundle(env.DB as any, tenant_id)
        const ir = loaded.bundle.core_ir as CoreIrV0
        const result = await store.execView({ tenant_id, ir, view_name, args: {} })
        return Response.json({ ok: true, result })
      }

      // POST /verify { tenant_id, entity_type, entity_id, limit? }
      if (url.pathname === "/verify" && req.method === "POST") {
        const body = (await req.json().catch(() => ({}))) as any
        const tenant_id = String(body.tenant_id ?? "t")
        const loaded = await loadTenantBundle(env.DB as any, tenant_id)
        const ir = loaded.bundle.core_ir as CoreIrV0
        const entity_type = String(body.entity_type ?? "")
        const entity_id = String(body.entity_id ?? "")
        const limit = Math.max(1, Math.min(Number(body.limit ?? 5000), 20000))

        if (!entity_type || !entity_id) return jsonErr(400, "entity_type and entity_id required")

        // Read events stream and verify against IR using oracle verifier.
        const stream = await store.readStream({ tenant_id, entity_type, entity_id, limit })

        // Adapt adapter rows into verifier Event format (payload_json -> payload object).
        const events = (stream.events ?? []).map((e: any) => ({
          tenant_id,
          entity_type,
          entity_id,
          seq: e.seq,
          event_type: e.event_type,
          payload: safeParseJson(e.payload_json),
          ts: e.ts,
          actor_id: e.actor_id,
        }))

        const report = verifyHistoryAgainstIr({
          bundle: { core_ir: ir },
          events,
          now: Math.floor(Date.now() / 1000),
          actor: "verifier",
          intrinsics,
          policies: {},
        })

        return Response.json({ ok: report.ok, report })
      }

      return jsonErr(404, "not found")
    } catch (e: any) {
      return jsonErr(500, e?.message ?? "error")
    }
  },
}

function jsonErr (status: number, message: string) {
  return new Response(JSON.stringify({ ok: false, error: message }), {
    status,
    headers: { "content-type": "application/json" },
  })
}

function safeParseJson (s: string) {
  try {
    return JSON.parse(s)
  } catch {
    return {}
  }
}
