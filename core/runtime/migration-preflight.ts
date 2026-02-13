import { validateBundleV0 } from "../ir/validate"
import type { VmEnv, VmIntrinsics } from "../vm/eval"
import { detectHistoryCorruption } from "./history-integrity"
import { verifyMigrationReplay, type MigrationVerifyReport } from "./migration-verify"
import type { Event } from "./replay"

export type PreflightCheck = {
  ok: boolean
  detail?: string
}

export type MigrationPreflightChecks = {
  from_bundle_valid: PreflightCheck
  to_bundle_valid: PreflightCheck
  migration_exists: PreflightCheck
  version_forward: PreflightCheck
  history_integrity: PreflightCheck
  replay_verification: PreflightCheck
}

export type MigrationPreflightReport = {
  ok: boolean
  migration_id: string
  checks: MigrationPreflightChecks
  verify?: MigrationVerifyReport
}

export function preflightMigration (params: {
  from_bundle: unknown
  to_bundle: unknown
  migration_id: string
  events: Event[]
  now: number
  actor: string
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
  expected_history_hash?: string
}): MigrationPreflightReport {
  const checks: MigrationPreflightChecks = {
    from_bundle_valid: { ok: false },
    to_bundle_valid: { ok: false },
    migration_exists: { ok: false },
    version_forward: { ok: false },
    history_integrity: { ok: false },
    replay_verification: { ok: false },
  }

  const fromV = validateBundleV0(params.from_bundle)
  checks.from_bundle_valid = fromV.ok
    ? { ok: true }
    : { ok: false, detail: fromV.errors[0]?.message ?? "invalid from_bundle" }
  if (!fromV.ok) return { ok: false, migration_id: params.migration_id, checks }

  const toV = validateBundleV0(params.to_bundle)
  checks.to_bundle_valid = toV.ok
    ? { ok: true }
    : { ok: false, detail: toV.errors[0]?.message ?? "invalid to_bundle" }
  if (!toV.ok) return { ok: false, migration_id: params.migration_id, checks }

  const migration = (toV.value as any).core_ir?.migrations?.[params.migration_id]
  checks.migration_exists = migration
    ? { ok: true }
    : { ok: false, detail: `missing migration '${params.migration_id}'` }
  if (!migration) return { ok: false, migration_id: params.migration_id, checks }

  const forward = Number(migration.from_version) < Number(migration.to_version)
  checks.version_forward = forward
    ? { ok: true }
    : { ok: false, detail: `non-forward migration: ${migration.from_version} -> ${migration.to_version}` }

  const corruption = detectHistoryCorruption({
    events: params.events,
    expected_hash: params.expected_history_hash,
  })
  checks.history_integrity = corruption.length === 0
    ? { ok: true }
    : { ok: false, detail: corruption[0]?.message ?? "history integrity check failed" }

  const verify = verifyMigrationReplay({
    from_bundle: params.from_bundle,
    to_bundle: params.to_bundle,
    migration_id: params.migration_id,
    events: params.events,
    now: params.now,
    actor: params.actor,
    intrinsics: params.intrinsics,
    policies: params.policies,
  })
  checks.replay_verification = verify.ok
    ? { ok: true }
    : { ok: false, detail: verify.error ?? "replay verification failed" }

  const ok =
    checks.from_bundle_valid.ok &&
    checks.to_bundle_valid.ok &&
    checks.migration_exists.ok &&
    checks.version_forward.ok &&
    checks.history_integrity.ok &&
    checks.replay_verification.ok

  return {
    ok,
    migration_id: params.migration_id,
    checks,
    verify,
  }
}
