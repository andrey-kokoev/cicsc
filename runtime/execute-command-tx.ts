// /runtime/execute-command-tx.ts

import type { CoreIrV0, ExprV0 } from "../core/ir/types"
import { evalExpr, type VmEnv, type VmIntrinsics, type Value } from "../core/vm/eval"
import { applyReducerOps, type Snapshot } from "../core/reducer/apply"
import type { D1Store } from "./db/d1-store"
import { runAllConstraints } from "../core/runtime/constraints"
import type { SnapRow } from "../core/query/interpret"

export type ExecuteCommandInput = {
  tenant_id: string
  actor_id: string
  command_id: string

  entity_type: string
  entity_id: string

  command_name: string
  input: Record<string, Value>

  now: number

  // optional constraint args, keyed by constraint_id
  constraint_args?: Record<string, Record<string, any>>
}

export type ExecuteCommandResult = {
  entity_id: string
  seq_from: number
  seq_to: number
  state: string
  updated_ts: number
}

type Tx = {
  // D1 batch is atomic in Workers when used as a transaction via "BEGIN ... COMMIT" on same connection.
  // Our adapter provides transactional ops; if not available, we emulate with explicit SQL begin/commit.
  exec: (sql: string, binds?: any[]) => Promise<{ rows?: any[] }>
}

export async function executeCommandTx (params: {
  ir: CoreIrV0
  store: D1Store
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
  req: ExecuteCommandInput
}): Promise<ExecuteCommandResult> {
  const { ir, store, intrinsics, policies, req } = params

  const typeSpec = ir.types[req.entity_type]
  if (!typeSpec) throw new Error(`unknown entity_type: ${req.entity_type}`)

  const cmd = typeSpec.commands[req.command_name]
  if (!cmd) throw new Error(`unknown command: ${req.entity_type}.${req.command_name}`)

  // NOTE: store/adapter currently does not expose a native tx API in our scaffold.
  // So we do best-effort "atomicity" by:
  // - writing command_receipts first (idempotency gate)
  // - if it already exists, return recorded result
  // - else, perform append+snapshot+constraints
  //
  // This is correct w.r.t. idempotency, but not fully serializable across concurrent commands.
  // Next tightening step: true transaction in adapter (BEGIN IMMEDIATE).
  //
  // For now this is still the right next file: it centralizes invariants and gives one place to add tx later.

  // 0) command receipt fast-path
  const existing = await tryReadReceipt(store, req.tenant_id, req.command_id)
  if (existing) return existing

  // 1) load snapshot
  const snapRow = await store.getSnapshot({
    tenant_id: req.tenant_id,
    entity_type: req.entity_type,
    entity_id: req.entity_id,
  })

  const snap: Snapshot = snapRow
    ? {
      state: snapRow.state,
      attrs: safeParseJson(snapRow.attrs_json) as any,
      shadows: extractShadows(snapRow, ["tenant_id", "entity_type", "entity_id", "state", "attrs_json", "updated_ts"]),
      updated_ts: snapRow.updated_ts,
    }
    : {
      state: typeSpec.initial_state,
      attrs: {},
      shadows: {},
      updated_ts: req.now,
    }

  // 2) guard
  const guardEnv: VmEnv = {
    now: req.now,
    actor: req.actor_id,
    state: snap.state,
    input: req.input ?? {},
    attrs: snap.attrs,
    row: {},
    arg: {},
    intrinsics,
    policies,
  }

  if (!toBool(evalExpr(cmd.guard.expr as any, guardEnv))) throw new Error("guard rejected")

  // 3) materialize events
  const events = cmd.emits.map((e) => {
    const payload: Record<string, Value> = {}
    for (const [k, ex] of Object.entries(e.payload)) payload[k] = evalExpr(ex as any, guardEnv)
    return {
      event_type: e.event_type,
      payload,
      ts: req.now,
      actor_id: req.actor_id,
    }
  })

  // 4) append events (idempotent by command_id)
  const append = await store.appendEvents({
    tenant_id: req.tenant_id,
    entity_type: req.entity_type,
    entity_id: req.entity_id,
    command_id: req.command_id,
    events: events.map((e) => ({ ...e, payload: e.payload })),
  })

  // 5) apply reducer
  let next = snap
  for (const e of events) {
    const ops = typeSpec.reducer[e.event_type]
    if (!ops) throw new Error(`missing reducer for event_type ${e.event_type}`)

    const reducerEnv: Omit<VmEnv, "row"> = {
      now: e.ts,
      actor: e.actor_id,
      state: next.state,
      input: {},
      attrs: next.attrs,
      row: {},
      arg: {},
      intrinsics,
      policies,
      e: { type: e.event_type, actor: e.actor_id, time: e.ts, payload: (e.payload as any) ?? {} },
    }

    next = applyReducerOps({
      snapshot: next,
      ops: ops as any,
      now: e.ts,
      eval: (expr: ExprV0) => evalExpr(expr, { ...(reducerEnv as any), row: {} }),
    })
  }

  // 6) enforce constraints before writing snapshot (logical tx)
  // Build snapshot rows for just this type (needed for snapshot constraints).
  const thisRow: SnapRow = {
    entity_type: req.entity_type,
    entity_id: req.entity_id,
    state: next.state,
    updated_ts: req.now,
    // flatten attrs + shadows (for v0 constraints that refer to row.field directly)
    ...(next.attrs as any),
    ...(next.shadows as any),
  }

  const violations = runAllConstraints({
    ir,
    intrinsics,
    policies,
    now: req.now,
    actor: req.actor_id,
    snapshotsByType: (t) => (t === req.entity_type ? [thisRow] : []),
    slaStatus: () => [],
  })

  if (violations.length) throw new Error(`constraint violated: ${violations[0]!.constraint_id}`)

  // bool_query constraints (global) via store (SQL) with args
  for (const [cid, c] of Object.entries(ir.constraints ?? {})) {
    if ((c as any).kind !== "bool_query") continue
    if ((c as any).on_type !== req.entity_type) continue

    const args = req.constraint_args?.[cid] ?? {}
    const ok = await store.checkBoolQueryConstraint({ tenant_id: req.tenant_id, ir, constraint_id: cid, args })
    if (!ok) throw new Error(`constraint violated: ${cid}`)
  }

  // 7) write snapshot
  await store.putSnapshot({
    tenant_id: req.tenant_id,
    entity_type: req.entity_type,
    entity_id: req.entity_id,
    state: next.state,
    attrs_json: stableJson(next.attrs),
    updated_ts: req.now,
    shadows: Object.keys(typeSpec.shadows ?? {}).length ? (next.shadows as any) : undefined,
  })

  const result: ExecuteCommandResult = { ...append, state: next.state, updated_ts: req.now }

  // 8) write receipt (for idempotency)
  await writeReceipt(store, req.tenant_id, req.command_id, req.entity_type, req.entity_id, result, req.now)

  return result
}

// ------------------------
// receipt helpers (requires adapter support via exec_view_sql)
// ------------------------

async function tryReadReceipt (store: D1Store, tenant_id: string, command_id: string): Promise<ExecuteCommandResult | null> {
  // D1Store doesn't expose receipt read yet; use adapter exec_view_sql via store.adapter.
  const r = await store.adapter.exec_view_sql({
    sql: `SELECT result_json FROM command_receipts WHERE tenant_id=? AND command_id=? LIMIT 1`,
    binds: [tenant_id, command_id],
  })
  const row = r.rows?.[0] as any
  if (!row) return null
  return safeParseJson(String(row.result_json ?? "{}")) as ExecuteCommandResult
}

async function writeReceipt (
  store: D1Store,
  tenant_id: string,
  command_id: string,
  entity_type: string,
  entity_id: string,
  result: ExecuteCommandResult,
  ts: number
) {
  await store.adapter.exec_view_sql({
    sql:
      `INSERT INTO command_receipts(tenant_id, command_id, entity_type, entity_id, result_json, ts)\n` +
      `VALUES(?,?,?,?,?,?)\n` +
      `ON CONFLICT(tenant_id, command_id) DO NOTHING`,
    binds: [tenant_id, command_id, entity_type, entity_id, JSON.stringify(result), ts],
  })
}

// ------------------------
// helpers
// ------------------------

function toBool (v: Value): boolean {
  if (v === null) return false
  if (typeof v === "boolean") return v
  if (typeof v === "number") return v !== 0
  if (typeof v === "string") return v.length > 0
  if (Array.isArray(v)) return v.length > 0
  return Object.keys(v).length > 0
}

function safeParseJson (s: string): any {
  try {
    const v = JSON.parse(s)
    return v && typeof v === "object" ? v : {}
  } catch {
    return {}
  }
}

function extractShadows (row: Record<string, any>, skip: string[]): Record<string, any> {
  const out: Record<string, any> = {}
  const skipSet = new Set(skip)
  for (const [k, v] of Object.entries(row)) {
    if (skipSet.has(k)) continue
    out[k] = v as any
  }
  return out
}

function stableJson (v: any): string {
  return JSON.stringify(sortKeys(v))
}

function sortKeys (v: any): any {
  if (v === null || typeof v !== "object") return v
  if (Array.isArray(v)) return v.map(sortKeys)
  const out: any = {}
  for (const k of Object.keys(v).sort()) out[k] = sortKeys(v[k])
  return out
}
