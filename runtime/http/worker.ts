// /runtime/http/worker.ts

import { makeD1Store } from "../db/d1-store"
import { executeCommandTx } from "../execute-command-tx"
import type { VmIntrinsics } from "../../core/vm/eval"

import { SqliteD1Adapter } from "../../adapters/sqlite/src/adapter"
import { genSqliteSchemaFromIr } from "../../adapters/sqlite/src/schema/gen"
import type { CoreIrV0 } from "../../core/ir/types"
import { validateBundleV0 } from "../../core/ir/validate"
import { verifyHistoryAgainstIr } from "../../core/runtime/verify"
import { activateVersion } from "../db/activate-version"
import { getBundle, putBundle } from "../db/bundle-registry"
import { bindTenant } from "../db/tenant-binding"
import { compileSpecToBundleV0, readSpecBody } from "./compile"
import { loadTenantBundle } from "./tenant-bundle"
import { TenantTokenBucketLimiter } from "./rate-limit"
import { applyRowLevelSecurity } from "../view/rls"

export interface Env {
  DB: D1Database
  BUNDLE_CREATE_TOKEN?: string
  TENANT_BIND_TOKEN?: string
  RATE_LIMIT_PER_MINUTE?: string
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
      const limiter = getLimiter(env.RATE_LIMIT_PER_MINUTE)

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

      // POST /compile  (compile + persist bundle, return bundle_hash)
      if (url.pathname === "/compile" && req.method === "POST") {
        if (!isAuthorized(req, env.BUNDLE_CREATE_TOKEN)) return jsonErr(403, "forbidden: bundle_create")
        const body = await readSpecBody(req)
        const bundle = compileSpecToBundleV0(body)
        const stored = await putBundle(env.DB as any, bundle)
        return Response.json({ ok: true, bundle, bundle_hash: stored.bundle_hash })
      }

      // POST /bundle  (stores bundle, returns bundle_hash)
      if (url.pathname === "/bundle" && req.method === "POST") {
        if (!isAuthorized(req, env.BUNDLE_CREATE_TOKEN)) return jsonErr(403, "forbidden: bundle_create")
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

      // GET /bundle/:hash  (retrieves bundle by hash)
      const getBundleMatch = url.pathname.match(/^\/bundle\/([^\/]+)$/)
      if (getBundleMatch && req.method === "GET") {
        const bundle_hash = decodeURIComponent(getBundleMatch[1]!)
        const bundle = await getBundle(env.DB as any, bundle_hash)
        if (!bundle) return jsonErr(404, "bundle not found")
        return Response.json({ ok: true, bundle })
      }

      // POST /bind  (bind tenant -> bundle_hash + active_version)
      if (url.pathname === "/bind" && req.method === "POST") {
        if (!isAuthorized(req, env.TENANT_BIND_TOKEN)) return jsonErr(403, "forbidden: tenant_bind")
        const body = (await req.json().catch(() => ({}))) as any
        const tenant_id = String(body.tenant_id ?? "")
        const bundle_hash = String(body.bundle_hash ?? "")
        const active_version = Number(body.active_version ?? 0)

        if (!tenant_id || !bundle_hash) return jsonErr(400, "tenant_id and bundle_hash required")
        if (!Number.isFinite(active_version) || active_version < 0) return jsonErr(400, "active_version must be >= 0")

        const bundle = await getBundle(env.DB as any, bundle_hash)
        if (!bundle) return jsonErr(404, "bundle not found")

        await bindTenant(env.DB as any, { tenant_id, bundle_hash, active_version })
        return Response.json({ ok: true })
      }

      // POST /install-from-spec  (compile + persist + bind tenant + install/activate)
      if (url.pathname === "/install-from-spec" && req.method === "POST") {
        const body = await readSpecBody(req)
        const bundle = compileSpecToBundleV0(body)
        const irV = bundle.core_ir as CoreIrV0

        const jsonBody = typeof body === "string" ? null : body
        const tenant_id =
          jsonBody && typeof jsonBody === "object" && (jsonBody as any).tenant_id
            ? String((jsonBody as any).tenant_id)
            : url.searchParams.get("tenant_id") ?? "t"

        const stored = await putBundle(env.DB as any, bundle)
        await bindTenant(env.DB as any, {
          tenant_id,
          bundle_hash: stored.bundle_hash,
          active_version: 0,
        })

        await activateVersion({
          db: env.DB as any,
          ir: irV,
          version: 0,
          tenant_id,
          setActiveVersion: store.setActiveVersion,
        })
        return Response.json({ ok: true, tenant_id, bundle_hash: stored.bundle_hash, active_version: 0 })
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

        if (limiter) {
          const allow = limiter.check(tenant_id, Date.now())
          if (!allow.ok) {
            return new Response(JSON.stringify({ ok: false, error: "rate limit exceeded" }), {
              status: 429,
              headers: {
                "content-type": "application/json",
                "retry-after": String(allow.retry_after_seconds ?? 1),
              },
            })
          }
        }

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
        const actor_id = url.searchParams.get("actor_id") ?? "u"
        const loaded = await loadTenantBundle(env.DB as any, tenant_id)
        const ir = loaded.bundle.core_ir as CoreIrV0
        const result = await store.execView({ tenant_id, ir, view_name, args: {} })
        const view: any = (ir.views ?? {})[view_name]
        const rows = view?.row_policy
          ? applyRowLevelSecurity({
            rows: result.rows,
            actor_id,
            row_policy: view.row_policy,
            intrinsics,
          })
          : result.rows
        return Response.json({ ok: true, result: { rows } })
      }

      // GET /views?tenant_id=...  (list available views)
      if (url.pathname === "/views" && req.method === "GET") {
        const tenant_id = url.searchParams.get("tenant_id") ?? "t"
        const loaded = await loadTenantBundle(env.DB as any, tenant_id)
        const ir = loaded.bundle.core_ir as CoreIrV0
        const views = Object.entries(ir.views ?? {}).map(([name, v]: [string, any]) => ({
          name,
          kind: String(v?.kind ?? "metric"),
          on_type: typeof v?.on_type === "string" ? v.on_type : null,
        }))
        return Response.json({ ok: true, views })
      }

      // GET /schema?tenant_id=...  (introspect generated schema for active tenant version)
      if (url.pathname === "/schema" && req.method === "GET") {
        const tenant_id = url.searchParams.get("tenant_id") ?? "t"
        const loaded = await loadTenantBundle(env.DB as any, tenant_id)
        const ir = loaded.bundle.core_ir as CoreIrV0
        const schema = genSqliteSchemaFromIr(ir, { version: loaded.active_version })
        return Response.json({
          ok: true,
          tenant_id,
          active_version: loaded.active_version,
          schema_sql: schema.sql,
        })
      }

      // POST /verify
      // - stream mode: { tenant_id, entity_type, entity_id, limit? }
      // - tenant mode: { tenant_id, limit? } (full-tenant verification)
      if (url.pathname === "/verify" && req.method === "POST") {
        const body = (await req.json().catch(() => ({}))) as any
        const tenant_id = String(body.tenant_id ?? "t")
        const loaded = await loadTenantBundle(env.DB as any, tenant_id)
        const ir = loaded.bundle.core_ir as CoreIrV0
        const entity_type = String(body.entity_type ?? "")
        const entity_id = String(body.entity_id ?? "")
        const limit = Math.max(1, Math.min(Number(body.limit ?? 5000), 20000))

        let events: any[]
        if (entity_type && entity_id) {
          const stream = await store.readStream({ tenant_id, entity_type, entity_id, limit })
          events = (stream.events ?? []).map((e: any) => ({
            tenant_id,
            entity_type,
            entity_id,
            seq: e.seq,
            event_type: e.event_type,
            payload: safeParseJson(e.payload_json),
            ts: e.ts,
            actor_id: e.actor_id,
          }))
        } else {
          const tenantEvents = await store.readTenantEvents({ tenant_id, limit: Math.max(limit, 50000) })
          events = (tenantEvents.events ?? []).map((e: any) => ({
            tenant_id: String(e.tenant_id ?? tenant_id),
            entity_type: String(e.entity_type ?? ""),
            entity_id: String(e.entity_id ?? ""),
            seq: Number(e.seq ?? 0),
            event_type: String(e.event_type ?? ""),
            payload: safeParseJson(String(e.payload_json ?? "{}")),
            ts: Number(e.ts ?? 0),
            actor_id: String(e.actor_id ?? "unknown"),
          }))
        }

        const report = verifyHistoryAgainstIr({
          bundle: { core_ir: ir },
          events,
          now: Math.floor(Date.now() / 1000),
          actor: "verifier",
          intrinsics,
          policies: {},
          version_stamp: {
            tenant_id,
            bundle_hash: loaded.bundle_hash,
            active_version: loaded.active_version,
          },
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

function isAuthorized (req: Request, expectedToken?: string): boolean {
  if (!expectedToken) return true
  const auth = req.headers.get("authorization") ?? ""
  const bearer = auth.startsWith("Bearer ") ? auth.slice("Bearer ".length).trim() : ""
  const alt = req.headers.get("x-cicsc-token") ?? ""
  const provided = bearer || alt
  return provided.length > 0 && provided === expectedToken
}

let _limiter: TenantTokenBucketLimiter | null = null
let _limiterCfg = ""

function getLimiter (ratePerMinuteRaw?: string): TenantTokenBucketLimiter | null {
  const n = Number(ratePerMinuteRaw ?? "0")
  if (!Number.isFinite(n) || n <= 0) return null
  const cfg = String(Math.trunc(n))
  if (!_limiter || _limiterCfg !== cfg) {
    const perMin = Math.max(1, Math.trunc(n))
    _limiter = new TenantTokenBucketLimiter(perMin, perMin / 60)
    _limiterCfg = cfg
  }
  return _limiter
}
