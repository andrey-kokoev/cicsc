import type { CoreIrBundleV0 } from "../ir/types"
import { validateBundleV0 } from "../ir/validate"
import type { VmEnv, VmIntrinsics } from "../vm/eval"
import { transformHistoryWithMigration } from "./migrate"
import type { Event } from "./replay"
import { verifyHistoryAgainstIr, type VerifyReport } from "./verify"

export type MigrationVerifyReport = {
  ok: boolean
  migration_id: string
  from_version: number
  to_version: number
  source_events: number
  migrated_events: number
  source_verify: VerifyReport
  target_verify: VerifyReport
  error?: string
}

export function verifyMigrationReplay (params: {
  from_bundle: unknown
  to_bundle: unknown
  migration_id: string
  events: Event[]
  now: number
  actor: string
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
}): MigrationVerifyReport {
  const fromV = validateBundleV0(params.from_bundle)
  if (!fromV.ok) {
    return failReport(params.migration_id, 0, 0, params.events.length, 0, `from_bundle invalid: ${fromV.errors[0]?.message ?? "unknown"}`)
  }

  const toV = validateBundleV0(params.to_bundle)
  if (!toV.ok) {
    return failReport(params.migration_id, 0, 0, params.events.length, 0, `to_bundle invalid: ${toV.errors[0]?.message ?? "unknown"}`)
  }

  const fromBundle = fromV.value as CoreIrBundleV0
  const toBundle = toV.value as CoreIrBundleV0
  const migration = toBundle.core_ir.migrations?.[params.migration_id]
  if (!migration) {
    return failReport(params.migration_id, 0, 0, params.events.length, 0, `missing migration '${params.migration_id}' in target bundle`)
  }

  const sourceVerify = verifyHistoryAgainstIr({
    bundle: fromBundle,
    events: params.events,
    now: params.now,
    actor: params.actor,
    intrinsics: params.intrinsics,
    policies: params.policies,
  })

  const migratedEvents = transformHistoryWithMigration({
    migration,
    events: params.events,
    intrinsics: params.intrinsics,
    policies: params.policies,
  })

  const targetVerify = verifyHistoryAgainstIr({
    bundle: toBundle,
    events: migratedEvents,
    now: params.now,
    actor: params.actor,
    intrinsics: params.intrinsics,
    policies: params.policies,
  })

  return {
    ok: sourceVerify.ok && targetVerify.ok,
    migration_id: params.migration_id,
    from_version: migration.from_version,
    to_version: migration.to_version,
    source_events: params.events.length,
    migrated_events: migratedEvents.length,
    source_verify: sourceVerify,
    target_verify: targetVerify,
  }
}

function failReport (
  migration_id: string,
  from_version: number,
  to_version: number,
  source_events: number,
  migrated_events: number,
  error: string
): MigrationVerifyReport {
  const empty: VerifyReport = {
    ok: false,
    core_ir_version: 0,
    types_count: 0,
    events_count: 0,
    entities_count: 0,
    constraints_count: 0,
    violations: [],
    ts: 0,
  }

  return {
    ok: false,
    migration_id,
    from_version,
    to_version,
    source_events,
    migrated_events,
    source_verify: empty,
    target_verify: empty,
    error,
  }
}
