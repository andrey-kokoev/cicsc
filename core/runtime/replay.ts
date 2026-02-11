// /core/runtime/replay.ts

import type { CoreIrV0, EntityTypeSpecV0, ExprV0, ReducerOpV0 } from "../ir/types"
import { applyReducerOps, type Snapshot } from "../reducer/apply"
import { evalExpr, type VmEnv, type VmIntrinsics, type Value } from "../vm/eval"

export type Event = {
  tenant_id: string
  entity_type: string
  entity_id: string
  seq: number
  event_type: string
  payload: Record<string, Value>
  ts: number
  actor_id: string
}

export type ReplayState = {
  state: string
  attrs: Record<string, Value>
  shadows: Record<string, Value>
  updated_ts: number
}

export type ReplayInputs = {
  ir: CoreIrV0
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
}

export function initialSnapshotForType (typeSpec: EntityTypeSpecV0, now: number): Snapshot {
  return {
    state: typeSpec.initial_state,
    attrs: {},
    shadows: {},
    updated_ts: now,
  }
}

export function replayStream (params: {
  inputs: ReplayInputs
  typeName: string
  entityId: string
  events: Event[]
  now?: number
}): ReplayState {
  const { inputs, typeName, events } = params

  const typeSpec = inputs.ir.types[typeName]
  if (!typeSpec) throw new Error(`replayStream: unknown type ${typeName}`)

  // Start from initial snapshot.
  let snap: Snapshot = initialSnapshotForType(typeSpec, params.now ?? 0)

  for (const e of events) {
    const ops = typeSpec.reducer[e.event_type]
    if (!ops) throw new Error(`replayStream: missing reducer for event_type ${e.event_type} on ${typeName}`)

    const envBase: Omit<VmEnv, "row"> = {
      now: e.ts,
      actor: e.actor_id,
      state: snap.state,
      input: {},
      attrs: snap.attrs,
      row: {},
      arg: {},
      intrinsics: inputs.intrinsics,
      policies: inputs.policies,
      e: { type: e.event_type, actor: e.actor_id, time: e.ts, payload: e.payload },
    }

    // Reducer expressions can reference $attrs, $state, and event payload via e_payload.
    snap = applyReducerOps({
      snapshot: snap,
      ops: ops as ReducerOpV0[],
      now: e.ts,
      eval: (expr: ExprV0) => evalExpr(expr, { ...(envBase as any), row: {} }),
    })
  }

  return { ...snap }
}

export function replayAllEntities (params: {
  inputs: ReplayInputs
  events: Event[]
}): Map<string, ReplayState> {
  const { inputs, events } = params

  // Group by (entity_type, entity_id)
  const groups = new Map<string, Event[]>()
  for (const e of events) {
    const key = `${e.entity_type}::${e.entity_id}`
    const arr = groups.get(key)
    if (arr) arr.push(e)
    else groups.set(key, [e])
  }

  // Ensure deterministic order: sort each stream by seq then ts.
  for (const arr of groups.values()) arr.sort((a, b) => a.seq - b.seq || a.ts - b.ts)

  const out = new Map<string, ReplayState>()
  for (const [key, stream] of Array.from(groups.entries()).sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))) {
    const [typeName, entityId] = key.split("::")
    out.set(key, replayStream({ inputs, typeName: typeName!, entityId: entityId!, events: stream }))
  }
  return out
}
