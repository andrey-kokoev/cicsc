import type { VmEnv, VmIntrinsics } from "../vm/eval"
import { preflightMigration, type MigrationPreflightReport } from "./migration-preflight"
import type { Event } from "./replay"

export type MigrationDryRunArtifact = {
  version: "cicsc/migration-dry-run-v1"
  generated_at: number
  migration_id: string
  ok: boolean
  source_events: number
  migrated_events: number
  preflight: MigrationPreflightReport
}

export type MigrationDryRunReport = {
  ok: boolean
  artifact: MigrationDryRunArtifact
}

export async function runMigrationDryRun (params: {
  from_bundle: unknown
  to_bundle: unknown
  migration_id: string
  events: Event[]
  now: number
  actor: string
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
  expected_history_hash?: string
  write_artifact?: (artifact: MigrationDryRunArtifact) => Promise<void> | void
}): Promise<MigrationDryRunReport> {
  const preflight = preflightMigration({
    from_bundle: params.from_bundle,
    to_bundle: params.to_bundle,
    migration_id: params.migration_id,
    events: params.events,
    now: params.now,
    actor: params.actor,
    intrinsics: params.intrinsics,
    policies: params.policies,
    expected_history_hash: params.expected_history_hash,
  })

  const artifact: MigrationDryRunArtifact = {
    version: "cicsc/migration-dry-run-v1",
    generated_at: Date.now(),
    migration_id: params.migration_id,
    ok: preflight.ok,
    source_events: params.events.length,
    migrated_events: preflight.verify?.migrated_events ?? 0,
    preflight,
  }

  if (params.write_artifact) {
    await params.write_artifact(artifact)
  }

  return {
    ok: preflight.ok,
    artifact,
  }
}
