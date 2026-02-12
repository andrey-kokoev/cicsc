import type { CoreIrV0, ExprV0 } from "../core/ir/types"
import { evalExpr, type VmEnv, type VmIntrinsics, type Value } from "../core/vm/eval"
import { applyReducerOps, type Snapshot } from "../core/reducer/apply"
import { runAllConstraints } from "../core/runtime/constraints"
import type { SnapRow } from "../core/query/interpret"
import { lowerBoolQueryConstraintToSql } from "../adapters/sqlite/src/lower/constraint-to-sql"

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

export async function executeCommandTx (params: {
  ir: CoreIrV0
  store: { adapter: { tx: <T>(fn: (tx: TxCtx) => Promise<T>) => Promise<T>; get_active_version: (tenant_id: string) => Promise<number> } }
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
  req: ExecuteCommandInput
}): Promise<ExecuteCommandResult> {
  const { ir, store, intrinsics, policies, req } = params

  const typeSpec = ir.types[req.entity_type]
  if (!typeSpec) throw new Error(`unknown entity_type: ${req.entity_type}`)

  const cmd = typeSpec.commands[req.command_name]
  if (!cmd) throw new Error(`unknown command: ${req.entity_type}.${req.command_name}`)

  return store.adapter.tx(async (tx) => {
    // 0) idempotency: receipt fast-path
    const existing = await readReceipt(tx, req.tenant_id, req.command_id)
    if (existing) return existing

    // 1) load snapshot (or init)
    const snapRow = await readSnapshot(tx, req.tenant_id, req.entity_type, req.entity_id)

    const snap: Snapshot = snapRow
      ? {
        state: snapRow.state,
        attrs: safeParseJson(snapRow.attrs_json) as any,
        shadows: pickShadows(snapRow, Object.keys(typeSpec.shadows ?? {})),
        updated_ts: snapRow.updated_ts,
      }
      : { state: typeSpec.initial_state, attrs: {}, shadows: {}, updated_ts: req.now }

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

    if (!toBool(evalExpr(cmd.guard.expr as any, guardEnv))) {
      throw new Error(`guard rejected: ${req.entity_type}.${req.command_name}`)
    }

    // 3) materialize events
    const events = cmd.emits.map((e) => {
      const payload: Record<string, Value> = {}
      for (const [k, ex] of Object.entries(e.payload)) payload[k] = evalExpr(ex as any, guardEnv)
      return { event_type: e.event_type, payload, ts: req.now, actor_id: req.actor_id }
    })

    // 4) append events with atomic seq allocation
    const { seq_from, seq_to } = await appendEventsTx(tx, {
      tenant_id: req.tenant_id,
      entity_type: req.entity_type,
      entity_id: req.entity_id,
      command_id: req.command_id,
      events,
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

    // 6) snapshot constraints across all constrained types (inside same tx)
    const snapshotConstraintTypes = listSnapshotConstraintTypes(ir)
    const snapshotRowsByType = new Map<string, SnapRow[]>()

    for (const t of snapshotConstraintTypes) {
      snapshotRowsByType.set(t, await readAllSnapshotsByType(tx, req.tenant_id, t))
    }

    if (snapshotRowsByType.has(req.entity_type)) {
      const thisRow: SnapRow = {
        entity_type: req.entity_type,
        entity_id: req.entity_id,
        state: next.state,
        updated_ts: req.now,
        ...(next.attrs as any),
        ...(next.shadows as any),
      }
      const rows = snapshotRowsByType.get(req.entity_type) ?? []
      upsertByEntityId(rows, thisRow)
      snapshotRowsByType.set(req.entity_type, rows)
    }

    const snapshotOnlyIr = {
      ...ir,
      constraints: Object.fromEntries(
        Object.entries(ir.constraints ?? {}).filter(([, c]) => (c as any).kind === "snapshot")
      ),
    } as CoreIrV0

    const snapshotViolations = runAllConstraints({
      ir: snapshotOnlyIr,
      intrinsics,
      policies,
      now: req.now,
      actor: req.actor_id,
      snapshotsByType: (t) => snapshotRowsByType.get(t) ?? [],
      slaStatus: () => [],
    }).filter((v) => v.kind === "snapshot")

    if (snapshotViolations.length) throw new Error(`constraint violated: ${snapshotViolations[0]!.constraint_id}`)

    // 7) bool_query constraints (run inside same tx using lowered SQL)
    const ver = await store.adapter.get_active_version(req.tenant_id)

    for (const [cid, c] of Object.entries(ir.constraints ?? {})) {
      if ((c as any).kind !== "bool_query") continue
      if ((c as any).on_type !== req.entity_type) continue

      const args = req.constraint_args?.[cid] ?? {}
      const plan = lowerBoolQueryConstraintToSql({
        constraint: c as any,
        version: ver,
        tenant_id: req.tenant_id,
        args,
      })

      const r = await tx.exec(plan.sql, plan.binds)
      const row = (r.rows?.[0] ?? null) as any
      const ok = row && (row.ok === 1 || row.ok === true)
      if (!ok) throw new Error(`constraint violated: ${cid}`)
    }

    // 8) write snapshot (including shadows)
    await upsertSnapshotTx(tx, {
      tenant_id: req.tenant_id,
      entity_type: req.entity_type,
      entity_id: req.entity_id,
      state: next.state,
      attrs_json: stableJson(next.attrs),
      updated_ts: req.now,
      shadows: Object.keys(typeSpec.shadows ?? {}).length ? (next.shadows as any) : {},
    })

    const result: ExecuteCommandResult = {
      entity_id: req.entity_id,
      seq_from,
      seq_to,
      state: next.state,
      updated_ts: req.now,
    }

    // 9) receipt
    await writeReceipt(tx, req.tenant_id, req.command_id, req.entity_type, req.entity_id, result, req.now)

    return result
  })
}

// --------------------------------
// Tx primitives
// --------------------------------

export type TxCtx = {
  exec: (sql: string, binds?: any[]) => Promise<{ rows?: any[] }>
}

async function readReceipt (tx: TxCtx, tenant_id: string, command_id: string): Promise<ExecuteCommandResult | null> {
  const r = await tx.exec(
    `SELECT result_json FROM command_receipts WHERE tenant_id=? AND command_id=? LIMIT 1`,
    [tenant_id, command_id]
  )
  const row = r.rows?.[0] as any
  if (!row) return null
  return safeParseJson(String(row.result_json ?? "{}")) as ExecuteCommandResult
}

async function writeReceipt (
  tx: TxCtx,
  tenant_id: string,
  command_id: string,
  entity_type: string,
  entity_id: string,
  result: ExecuteCommandResult,
  ts: number
) {
  await tx.exec(
    `INSERT INTO command_receipts(tenant_id, command_id, entity_type, entity_id, result_json, ts)
     VALUES(?,?,?,?,?,?)
     ON CONFLICT(tenant_id, command_id) DO NOTHING`,
    [tenant_id, command_id, entity_type, entity_id, JSON.stringify(result), ts]
  )
}

async function readSnapshot (
  tx: TxCtx,
  tenant_id: string,
  entity_type: string,
  entity_id: string
): Promise<{ state: string; attrs_json: string; updated_ts: number;[k: string]: any } | null> {
  const r = await tx.exec(
    `SELECT state, attrs_json, updated_ts, severity_i, created_at
     FROM snapshots_v0
     WHERE tenant_id=? AND entity_type=? AND entity_id=?
     LIMIT 1`,
    [tenant_id, entity_type, entity_id]
  )
  return (r.rows?.[0] as any) ?? null
}

async function upsertSnapshotTx (tx: TxCtx, p: {
  tenant_id: string
  entity_type: string
  entity_id: string
  state: string
  attrs_json: string
  updated_ts: number
  shadows: Record<string, any>
}) {
  // v0: we only persist known shadow columns we created in install-schema.ts (severity_i, created_at).
  const severity_i = p.shadows["severity_i"] ?? null
  const created_at = p.shadows["created_at"] ?? null

  await tx.exec(
    `INSERT INTO snapshots_v0(tenant_id, entity_type, entity_id, state, attrs_json, updated_ts, severity_i, created_at)
     VALUES(?,?,?,?,?,?,?,?)
     ON CONFLICT(tenant_id, entity_type, entity_id) DO UPDATE SET
       state=excluded.state,
       attrs_json=excluded.attrs_json,
       updated_ts=excluded.updated_ts,
       severity_i=excluded.severity_i,
       created_at=excluded.created_at`,
    [p.tenant_id, p.entity_type, p.entity_id, p.state, p.attrs_json, p.updated_ts, severity_i, created_at]
  )
}

async function appendEventsTx (tx: TxCtx, p: {
  tenant_id: string
  entity_type: string
  entity_id: string
  command_id: string
  events: { event_type: string; payload: unknown; ts: number; actor_id: string }[]
}): Promise<{ seq_from: number; seq_to: number }> {
  if (!p.events.length) return { seq_from: 0, seq_to: 0 }

  const r = await tx.exec(
    `SELECT COALESCE(MAX(seq), 0) AS max_seq
     FROM events_v0
     WHERE tenant_id=? AND entity_type=? AND entity_id=?`,
    [p.tenant_id, p.entity_type, p.entity_id]
  )
  const maxSeq = Number((r.rows?.[0] as any)?.max_seq ?? 0)
  const seq_from = maxSeq + 1
  const seq_to = maxSeq + p.events.length

  // Multi-row insert (including command_id for event-level traceability)
  const values: string[] = []
  const binds: any[] = []
  let seq = seq_from

  for (const e of p.events) {
    values.push("(?,?,?,?,?,?,?,?,?)")
    binds.push(
      p.tenant_id,
      p.entity_type,
      p.entity_id,
      seq,
      e.event_type,
      JSON.stringify(e.payload ?? {}),
      e.ts,
      e.actor_id,
      p.command_id
    )
    seq++
  }

  await tx.exec(
    `INSERT INTO events_v0(tenant_id, entity_type, entity_id, seq, event_type, payload_json, ts, actor_id, command_id)
     VALUES ${values.join(", ")}`,
    binds
  )

  return { seq_from, seq_to }
}

async function readAllSnapshotsByType (tx: TxCtx, tenant_id: string, entity_type: string): Promise<SnapRow[]> {
  const r = await tx.exec(
    `SELECT *
     FROM snapshots_v0
     WHERE tenant_id=? AND entity_type=?`,
    [tenant_id, entity_type]
  )
  const rows = (r.rows ?? []) as any[]
  return rows.map(toSnapRow)
}

// --------------------------------
// helpers
// --------------------------------

function listSnapshotConstraintTypes (ir: CoreIrV0): string[] {
  const out = new Set<string>()
  for (const c of Object.values(ir.constraints ?? {})) {
    if ((c as any).kind === "snapshot") out.add(String((c as any).on_type))
  }
  return Array.from(out)
}

function upsertByEntityId (rows: SnapRow[], row: SnapRow): void {
  const id = String((row as any).entity_id ?? "")
  const i = rows.findIndex((r) => String((r as any).entity_id ?? "") === id)
  if (i >= 0) rows[i] = row
  else rows.push(row)
}

function toSnapRow (raw: Record<string, any>): SnapRow {
  const out: SnapRow = {
    entity_type: String(raw.entity_type ?? ""),
    entity_id: String(raw.entity_id ?? ""),
    state: String(raw.state ?? ""),
    updated_ts: Number(raw.updated_ts ?? 0),
  }

  const attrs = safeParseJson(String(raw.attrs_json ?? "{}"))
  for (const [k, v] of Object.entries(attrs)) (out as any)[k] = v as any

  for (const [k, v] of Object.entries(raw)) {
    if (k === "tenant_id" || k === "entity_type" || k === "entity_id" || k === "state" || k === "attrs_json" || k === "updated_ts") continue
    ;(out as any)[k] = v as any
  }

  return out
}

function pickShadows (row: Record<string, any>, names: string[]): Record<string, any> {
  const out: Record<string, any> = {}
  for (const n of names) if (n in row) out[n] = row[n]
  return out
}

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
