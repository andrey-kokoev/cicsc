// /runtime/db/d1-store.ts

import type { CoreIrV0, ExprV0 } from "../../core/ir/types"
import { evalExpr, type VmEnv, type VmIntrinsics, type Value } from "../../core/vm/eval"
import type { SqliteD1Adapter } from "../../adapters/sqlite/src/adapter"
import { lowerQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"
import { lowerBoolQueryConstraintToSql } from "../../adapters/sqlite/src/lower/constraint-to-sql"
import { interpretQuery } from "../../core/query/interpret"

export type D1Store = {
  adapter: SqliteD1Adapter

  getActiveVersion: (tenant_id: string) => Promise<number>
  setActiveVersion: (tenant_id: string, version: number) => Promise<void>

  appendEvents: (params: {
    tenant_id: string
    entity_type: string
    entity_id: string
    command_id: string
    events: { event_type: string; payload: unknown; ts: number; actor_id: string }[]
  }) => Promise<{ entity_id: string; seq_from: number; seq_to: number }>

  getSnapshot: (params: { tenant_id: string; entity_type: string; entity_id: string }) => Promise<{
    tenant_id: string
    entity_type: string
    entity_id: string
    state: string
    attrs_json: string
    updated_ts: number;
    [k: string]: any
  } | null>

  putSnapshot: (params: {
    tenant_id: string
    entity_type: string
    entity_id: string
    state: string
    attrs_json: string
    updated_ts: number
    shadows?: Record<string, string | number | null>
  }) => Promise<void>

  // Read full stream for verify/migrations later
  readStream: (params: {
    tenant_id: string
    entity_type: string
    entity_id: string
    from_seq?: number
    limit?: number
  }) => Promise<{ events: any[]; next_seq?: number }>

  // Views / constraints executed via lowered SQL (preferred), with oracle fallback (development)
  execView: (params: {
    tenant_id: string
    ir: CoreIrV0
    view_name: string
    args?: Record<string, any>
  }) => Promise<{ rows: any[] }>

  checkBoolQueryConstraint: (params: {
    tenant_id: string
    ir: CoreIrV0
    constraint_id: string
    args?: Record<string, any>
  }) => Promise<boolean>
}

export function makeD1Store (params: { adapter: SqliteD1Adapter }): D1Store {
  const { adapter } = params

  return {
    adapter,

    getActiveVersion: (tenant_id) => adapter.get_active_version(tenant_id),
    setActiveVersion: (tenant_id, version) => adapter.set_active_version(tenant_id, version),

    appendEvents: (p) => adapter.append_events(p),

    getSnapshot: (p) => adapter.get_snapshot(p) as any,

    putSnapshot: (p) => adapter.put_snapshot(p),

    readStream: async ({ tenant_id, entity_type, entity_id, from_seq, limit }) => {
      const out = await adapter.read_stream({
        tenant_id,
        entity_type,
        entity_id,
        from: from_seq != null ? { seq: from_seq } : undefined,
        limit,
      })
      return { events: out.events, next_seq: out.next?.seq }
    },

    execView: async ({ tenant_id, ir, view_name, args }) => {
      const view = ir.views?.[view_name]
      if (!view) throw new Error(`unknown view: ${view_name}`)

      const ver = await adapter.get_active_version(tenant_id)

      // Lower query to SQL and execute.
      // Source binds are inferred in the constraint lowering right now; for view we inline them here.
      const plan = lowerQueryToSql(view.query as any, { version: ver, tenant_id })
      const binds = [...inferSourceBinds((view.query as any).source, tenant_id), ...plan.binds]

      // Replace arg sentinels (if any) using args
      const replaced = replaceArgSentinels(plan.sql, binds, args ?? {})
      const r = await adapter.exec_view_sql({ sql: replaced.sql, binds: replaced.binds })
      return { rows: r.rows }
    },

    checkBoolQueryConstraint: async ({ tenant_id, ir, constraint_id, args }) => {
      const c = ir.constraints?.[constraint_id]
      if (!c) throw new Error(`unknown constraint: ${constraint_id}`)
      if ((c as any).kind !== "bool_query") throw new Error(`constraint ${constraint_id} is not bool_query`)

      const ver = await adapter.get_active_version(tenant_id)
      const plan = lowerBoolQueryConstraintToSql({
        constraint: c as any,
        version: ver,
        tenant_id,
        args: args ?? {},
      })

      const rows = await adapter.exec_view_sql({ sql: plan.sql, binds: plan.binds })
      const row = rows.rows[0] as any
      if (!row) throw new Error("constraint SQL returned no rows")
      return row.ok === 1 || row.ok === true
    },
  }
}

// ------------------------
// Helpers (shared lowering glue)
// ------------------------

function inferSourceBinds (src: any, tenant_id: string): any[] {
  const tag = soleKey(src)
  const body: any = src[tag]

  if (tag === "snap") return [tenant_id, String(body.type)]
  if (tag === "sla_status") return [tenant_id, String(body.name), String(body.on_type)]
  if (tag === "join") return [...inferSourceBinds(body.left, tenant_id), ...inferSourceBinds(body.right, tenant_id)]
  throw new Error(`inferSourceBinds: unsupported source tag ${tag}`)
}

function replaceArgSentinels (sql: string, binds: any[], args: Record<string, any>): { sql: string; binds: any[] } {
  // Query lowering emits __ARG__name__ in rare cases (mostly constraints). Keep support.
  const re = /__ARG__([A-Za-z0-9_"]+?)__/g
  const outBinds: any[] = [...binds]

  let outSql = ""
  let last = 0
  let m: RegExpExecArray | null

  while ((m = re.exec(sql))) {
    outSql += sql.slice(last, m.index) + "?"
    const raw = m[1]!
    const name = raw.replaceAll(`"`, "")
    outBinds.push(args[name] ?? null)
    last = m.index + m[0].length
  }
  outSql += sql.slice(last)

  return { sql: outSql, binds: outBinds }
}

function soleKey (o: any): string {
  const ks = Object.keys(o)
  if (ks.length !== 1) throw new Error("invalid tagged object")
  return ks[0]!
}
