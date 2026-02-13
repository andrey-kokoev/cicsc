import type { CoreIrBundleV0, MigrationSpecV0 } from "../ir/types"
import type { VmEnv, VmIntrinsics } from "../vm/eval"
import { transformHistoryWithMigration } from "./migrate"
import type { Event } from "./replay"

export type RollbackReport = {
  ok: boolean
  migration_id: string
  rolled_back_events: number
  error?: string
}

export function rollbackMigrationChain (params: {
  to_bundle: CoreIrBundleV0 | unknown
  migration_id: string
  events: Event[]
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
}): RollbackReport & { events?: Event[] } {
  const migration = (params.to_bundle as any)?.core_ir?.migrations?.[params.migration_id] as MigrationSpecV0 | undefined
  if (!migration) {
    return fail(params.migration_id, params.events.length, `missing migration '${params.migration_id}'`)
  }

  const inv = inverseMigrationForRollback(migration)
  if (!inv.ok || !inv.value) {
    return fail(params.migration_id, params.events.length, inv.error ?? "inverse migration unavailable")
  }

  const rolledBack = transformHistoryWithMigration({
    migration: inv.value,
    events: params.events,
    intrinsics: params.intrinsics,
    policies: params.policies,
  })

  return {
    ok: true,
    migration_id: params.migration_id,
    rolled_back_events: rolledBack.length,
    events: rolledBack,
  }
}

export function inverseMigrationForRollback (migration: MigrationSpecV0): { ok: true; value: MigrationSpecV0 } | { ok: false; error: string } {
  const inverseEventTransforms: Record<string, NonNullable<MigrationSpecV0["event_transforms"]>[string]> = {}
  const seenTargets = new Set<string>()

  for (const [sourceEvent, tr] of Object.entries(migration.event_transforms ?? {})) {
    if (tr.drop) {
      return { ok: false, error: `non-reversible migration: dropped event '${sourceEvent}'` }
    }
    if (tr.payload_map && Object.keys(tr.payload_map).length > 0) {
      return { ok: false, error: `non-reversible migration: payload_map on '${sourceEvent}'` }
    }

    const targetEvent = tr.emit_as ?? sourceEvent
    if (seenTargets.has(targetEvent)) {
      return { ok: false, error: `non-reversible migration: non-injective event mapping to '${targetEvent}'` }
    }
    seenTargets.add(targetEvent)
    inverseEventTransforms[targetEvent] = { emit_as: sourceEvent }
  }

  const inverseStateMap: Record<string, string> = {}
  const seenStateTargets = new Set<string>()
  for (const [fromState, toState] of Object.entries(migration.state_map ?? {})) {
    if (seenStateTargets.has(toState)) {
      return { ok: false, error: `non-reversible migration: non-injective state map to '${toState}'` }
    }
    seenStateTargets.add(toState)
    inverseStateMap[toState] = fromState
  }

  return {
    ok: true,
    value: {
      from_version: migration.to_version,
      to_version: migration.from_version,
      on_type: migration.on_type,
      event_transforms: inverseEventTransforms,
      state_map: inverseStateMap,
    },
  }
}

function fail (migration_id: string, rolled_back_events: number, error: string): RollbackReport {
  return {
    ok: false,
    migration_id,
    rolled_back_events,
    error,
  }
}
