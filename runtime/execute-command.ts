// /runtime/execute-command.ts

import type { CoreIrV0, ExprV0 } from "../core/ir/types"
import { evalExpr, type VmEnv, type VmIntrinsics, type Value } from "../core/vm/eval"
import { applyReducerOps, type Snapshot } from "../core/reducer/apply"
import type { D1Store } from "./db/d1-store"
import { ScheduleManager } from "./schedule/manager"

export type ExecuteCommandInput = {
  tenant_id: string
  actor_id: string
  command_id: string

  entity_type: string
  entity_id: string

  command_name: string
  input: Record<string, Value>

  now: number
}

export type ExecuteCommandResult = {
  entity_id: string
  seq_from: number
  seq_to: number
  state: string
  updated_ts: number
}

export async function executeCommand (params: {
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

  // Load snapshot (or initialize).
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

  // Guard eval env.
  const env: VmEnv = {
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

  const guardOk = toBool(evalExpr(cmd.guard.expr as any, env))
  if (!guardOk) throw new Error("guard rejected")

  // Produce events.
  const events = cmd.emits.map((e) => {
    const payload: Record<string, Value> = {}
    for (const [k, ex] of Object.entries(e.payload)) payload[k] = evalExpr(ex as any, env)
    return {
      event_type: e.event_type,
      payload,
      ts: req.now,
      actor_id: req.actor_id,
    }
  })

  // Append events (idempotent by command_id).
  const append = await store.appendEvents({
    tenant_id: req.tenant_id,
    entity_type: req.entity_type,
    entity_id: req.entity_id,
    command_id: req.command_id,
    events: events.map((e) => ({ ...e, payload: e.payload })),
  })

  // Apply reducer for those events to update snapshot.
  // Reducer env must see event payload via e_payload.
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

  // Write snapshot.
  // Shadows: for now we persist only those already present in row; computing shadow exprs is a later step.
  await store.putSnapshot({
    tenant_id: req.tenant_id,
    entity_type: req.entity_type,
    entity_id: req.entity_id,
    state: next.state,
    attrs_json: stableJson(next.attrs),
    updated_ts: req.now,
    shadows: (Object.keys(typeSpec.shadows ?? {}).length ? (next.shadows as any) : undefined) ?? undefined,
  })

  // Enforce bool_query constraints (global) that apply to this entity type.
  // Snapshot constraints are assumed to be handled via verifier or moved into DB checks later.
  for (const [cid, c] of Object.entries(ir.constraints ?? {})) {
    if ((c as any).kind !== "bool_query") continue
    if ((c as any).on_type !== req.entity_type) continue

    const ok = await store.checkBoolQueryConstraint({ tenant_id: req.tenant_id, ir, constraint_id: cid, args: {} })
    if (!ok) throw new Error(`constraint violated: ${cid}`)
  }

  // Hook into schedules
  const scheduleManager = new ScheduleManager(store, ir, intrinsics)
  await scheduleManager.onEventsEmitted({
    tenant_id: req.tenant_id,
    entity_type: req.entity_type,
    entity_id: req.entity_id,
    events,
    env: {
      state: snap.state,
      input: req.input as any,
      attrs: snap.attrs,
      policies,
    },
  })

  return { ...append, state: next.state, updated_ts: req.now }
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
    // D1 returns all selected columns; our get_snapshot selects core columns only, so this is mostly empty.
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
