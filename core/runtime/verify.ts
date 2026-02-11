// /core/runtime/verify.ts

import type { CoreIrBundleV0, CoreIrV0 } from "../ir/types"
import { validateBundleV0 } from "../ir/validate"
import type { VmIntrinsics } from "../vm/eval"
import { replayAllEntities, type Event } from "./replay"
import { runAllConstraints, type ConstraintViolation } from "./constraints"

export type VerifyReport = {
  ok: boolean

  core_ir_version: number
  types_count: number

  events_count: number
  entities_count: number

  constraints_count: number
  violations: ConstraintViolation[]

  ts: number
}

export function verifyHistoryAgainstIr (params: {
  bundle: unknown
  irOverride?: CoreIrV0
  events: Event[]

  now: number
  actor: string

  intrinsics: VmIntrinsics
  policies?: any
}): VerifyReport {
  const validated = validateBundleV0(params.bundle)
  if (!validated.ok) {
    return {
      ok: false,
      core_ir_version: -1,
      types_count: 0,
      events_count: params.events.length,
      entities_count: 0,
      constraints_count: 0,
      violations: validated.errors.map((e) => ({
        constraint_id: "bundle",
        kind: "snapshot",
        on_type: "?",
        message: `${e.path}: ${e.message}`,
      })),
      ts: params.now,
    }
  }

  const ir = params.irOverride ?? (validated.value.core_ir as CoreIrV0)

  const replayed = replayAllEntities({
    inputs: { ir, intrinsics: params.intrinsics, policies: params.policies },
    events: params.events,
  })

  // Build snapshot rows for queries/constraints. Convention: flatten minimal fields.
  const byType = new Map<string, any[]>()
  for (const [key, snap] of replayed.entries()) {
    const [entity_type, entity_id] = key.split("::")
    const row: any = {
      entity_type,
      entity_id,
      state: snap.state,
      updated_ts: snap.updated_ts,
      ...snap.attrs,
      ...snap.shadows,
    }
    const arr = byType.get(entity_type!)
    if (arr) arr.push(row)
    else byType.set(entity_type!, [row])
  }
  for (const arr of byType.values()) arr.sort((a, b) => String(a.entity_id).localeCompare(String(b.entity_id)))

  const violations = runAllConstraints({
    ir,
    intrinsics: params.intrinsics,
    policies: params.policies,
    now: params.now,
    actor: params.actor,
    snapshotsByType: (t) => byType.get(t) ?? [],
    slaStatus: () => [],
  })

  return {
    ok: violations.length === 0,
    core_ir_version: ir.version,
    types_count: Object.keys(ir.types).length,
    events_count: params.events.length,
    entities_count: replayed.size,
    constraints_count: Object.keys(ir.constraints ?? {}).length,
    violations,
    ts: params.now,
  }
}
