// /core/runtime/verify.ts

import type { CoreIrBundleV0, CoreIrV0 } from "../ir/types"
import { validateBundleV0 } from "../ir/validate"
import type { VmIntrinsics } from "../vm/eval"
import { replayAllEntities, replayStream, type Event } from "./replay"
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
  version_stamp?: {
    tenant_id?: string
    bundle_hash?: string
    active_version?: number
    verified_at_ts: number
  }
}

export function verifyHistoryAgainstIr (params: {
  bundle: unknown
  irOverride?: CoreIrV0
  events: Event[]

  now: number
  actor: string

  intrinsics: VmIntrinsics
  policies?: any
  version_stamp?: {
    tenant_id?: string
    bundle_hash?: string
    active_version?: number
  }
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
      version_stamp: {
        tenant_id: params.version_stamp?.tenant_id,
        bundle_hash: params.version_stamp?.bundle_hash,
        active_version: params.version_stamp?.active_version,
        verified_at_ts: params.now,
      },
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
    version_stamp: {
      tenant_id: params.version_stamp?.tenant_id,
      bundle_hash: params.version_stamp?.bundle_hash,
      active_version: params.version_stamp?.active_version,
      verified_at_ts: params.now,
    },
  }
}

export async function verifyHistoryAgainstIrStream (params: {
  bundle: unknown
  irOverride?: CoreIrV0
  events: AsyncIterable<Event>

  now: number
  actor: string

  intrinsics: VmIntrinsics
  policies?: any
  max_entities?: number
}): Promise<VerifyReport> {
  const validated = validateBundleV0(params.bundle)
  if (!validated.ok) {
    return {
      ok: false,
      core_ir_version: -1,
      types_count: 0,
      events_count: 0,
      entities_count: 0,
      constraints_count: 0,
      violations: validated.errors.map((e) => ({
        constraint_id: "bundle",
        kind: "snapshot",
        on_type: "?",
        message: `${e.path}: ${e.message}`,
      })),
      ts: params.now,
      version_stamp: {
        verified_at_ts: params.now,
      },
    }
  }

  const ir = params.irOverride ?? (validated.value.core_ir as CoreIrV0)
  const byType = new Map<string, any[]>()

  let eventsCount = 0
  let entitiesCount = 0
  let curKey = ""
  let curType = ""
  let curEntity = ""
  let curEvents: Event[] = []

  const flush = () => {
    if (!curKey) return
    const snap = replayStream({
      inputs: { ir, intrinsics: params.intrinsics, policies: params.policies },
      typeName: curType,
      entityId: curEntity,
      events: curEvents,
    })
    const row: any = {
      entity_type: curType,
      entity_id: curEntity,
      state: snap.state,
      updated_ts: snap.updated_ts,
      ...snap.attrs,
      ...snap.shadows,
    }
    const arr = byType.get(curType)
    if (arr) arr.push(row)
    else byType.set(curType, [row])

    entitiesCount++
    if (params.max_entities != null && entitiesCount > params.max_entities) {
      throw new Error(`stream verify exceeded max_entities=${params.max_entities}`)
    }
    curKey = ""
    curType = ""
    curEntity = ""
    curEvents = []
  }

  try {
    for await (const e of params.events) {
      eventsCount++
      const key = `${e.entity_type}::${e.entity_id}`
      if (!curKey) {
        curKey = key
        curType = e.entity_type
        curEntity = e.entity_id
      } else if (key !== curKey) {
        flush()
        curKey = key
        curType = e.entity_type
        curEntity = e.entity_id
      }
      curEvents.push(e)
    }
    flush()
  } catch (e: any) {
    return {
      ok: false,
      core_ir_version: ir.version,
      types_count: Object.keys(ir.types).length,
      events_count: eventsCount,
      entities_count: entitiesCount,
      constraints_count: Object.keys(ir.constraints ?? {}).length,
      violations: [{
        constraint_id: "streaming",
        kind: "snapshot",
        on_type: "*",
        message: e?.message ?? String(e),
      }],
      ts: params.now,
      version_stamp: {
        verified_at_ts: params.now,
      },
    }
  }

  for (const arr of byType.values()) {
    arr.sort((a, b) => String(a.entity_id).localeCompare(String(b.entity_id)))
  }

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
    events_count: eventsCount,
    entities_count: entitiesCount,
    constraints_count: Object.keys(ir.constraints ?? {}).length,
    violations,
    ts: params.now,
    version_stamp: {
      verified_at_ts: params.now,
    },
  }
}
