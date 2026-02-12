import type { MigrationSpecV0 } from "../ir/types"
import type { VmEnv, VmIntrinsics, Value } from "../vm/eval"
import { evalExpr } from "../vm/eval"
import type { Event } from "./replay"

export function transformHistoryWithMigration (params: {
  migration: MigrationSpecV0
  events: Event[]
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
}): Event[] {
  const { migration, events, intrinsics, policies } = params

  const out: Event[] = []
  for (const e of stableSortEvents(events)) {
    if (e.entity_type !== migration.on_type) {
      out.push({ ...e })
      continue
    }

    const t = migration.event_transforms?.[e.event_type]
    if (t?.drop) continue

    out.push({
      ...e,
      event_type: t?.emit_as ?? e.event_type,
      payload: mapPayload({
        sourcePayload: e.payload,
        payloadMap: t?.payload_map,
        event: e,
        intrinsics,
        policies,
      }),
    })
  }

  return resequenceByStream(out)
}

function mapPayload (params: {
  sourcePayload: Record<string, Value>
  payloadMap?: Record<string, any>
  event: Event
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
}): Record<string, Value> {
  const { sourcePayload, payloadMap, event, intrinsics, policies } = params
  if (!payloadMap || Object.keys(payloadMap).length === 0) return { ...sourcePayload }

  const env: VmEnv = {
    now: event.ts,
    actor: event.actor_id,
    state: "",
    input: {},
    attrs: {},
    row: {},
    arg: {},
    e: {
      type: event.event_type,
      actor: event.actor_id,
      time: event.ts,
      payload: sourcePayload,
    },
    intrinsics,
    policies,
  }

  const out: Record<string, Value> = {}
  for (const [k, expr] of Object.entries(payloadMap)) {
    out[k] = evalExpr(expr as any, env)
  }
  return out
}

function stableSortEvents (events: Event[]): Event[] {
  return [...events].sort((a, b) => {
    const ka = `${a.tenant_id}|${a.entity_type}|${a.entity_id}`
    const kb = `${b.tenant_id}|${b.entity_type}|${b.entity_id}`
    if (ka < kb) return -1
    if (ka > kb) return 1
    if (a.seq !== b.seq) return a.seq - b.seq
    return a.ts - b.ts
  })
}

function resequenceByStream (events: Event[]): Event[] {
  const next = new Map<string, number>()
  const out: Event[] = []
  for (const e of stableSortEvents(events)) {
    const key = `${e.tenant_id}|${e.entity_type}|${e.entity_id}`
    const seq = (next.get(key) ?? 0) + 1
    next.set(key, seq)
    out.push({ ...e, seq })
  }
  return out
}
