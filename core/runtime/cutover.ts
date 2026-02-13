import type { CoreIrBundleV0 } from "../ir/types"
import type { VmEnv, VmIntrinsics } from "../vm/eval"
import { transformHistoryWithMigration } from "./migrate"
import type { Event } from "./replay"
import { verifyMigrationReplay, type MigrationVerifyReport } from "./migration-verify"

export type CutoverReport = {
  ok: boolean
  mode: "pause_migrate_resume"
  migration_id: string
  from_version: number
  to_version: number
  migrated_events: number
  boundaries: {
    paused_at: number
    verified_at?: number
    switched_at?: number
    resumed_at: number
  }
  verify: MigrationVerifyReport
  error?: string
}

export async function cutoverPauseMigrateResume (params: {
  tenant_id: string
  migration_id: string
  from_bundle: CoreIrBundleV0 | unknown
  to_bundle: CoreIrBundleV0 | unknown
  now: number
  actor: string
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]
  pause_tenant: (tenant_id: string) => Promise<void>
  resume_tenant: (tenant_id: string) => Promise<void>
  load_source_history: () => Promise<Event[]>
  write_target_history: (events: Event[]) => Promise<void>
  set_active_version: (tenant_id: string, version: number) => Promise<void>
}): Promise<CutoverReport> {
  const pausedAt = Date.now()
  await params.pause_tenant(params.tenant_id)
  let report: CutoverReport | null = null

  try {
    const sourceEvents = await params.load_source_history()
    const verify = verifyMigrationReplay({
      from_bundle: params.from_bundle,
      to_bundle: params.to_bundle,
      migration_id: params.migration_id,
      events: sourceEvents,
      now: params.now,
      actor: params.actor,
      intrinsics: params.intrinsics,
      policies: params.policies,
    })
    if (!verify.ok) {
      report = {
        ok: false,
        mode: "pause_migrate_resume",
        migration_id: params.migration_id,
        from_version: verify.from_version,
        to_version: verify.to_version,
        migrated_events: 0,
        boundaries: {
          paused_at: pausedAt,
          resumed_at: pausedAt,
        },
        verify,
        error: verify.error ?? "migration replay verification failed",
      }
      return report
    }
    const verifiedAt = Date.now()

    const migration = (params.to_bundle as any)?.core_ir?.migrations?.[params.migration_id]
    const migratedEvents = transformHistoryWithMigration({
      migration,
      events: sourceEvents,
      intrinsics: params.intrinsics,
      policies: params.policies,
    })

    await params.write_target_history(migratedEvents)
    await params.set_active_version(params.tenant_id, verify.to_version)
    const switchedAt = Date.now()

    report = {
      ok: true,
      mode: "pause_migrate_resume",
      migration_id: params.migration_id,
      from_version: verify.from_version,
      to_version: verify.to_version,
      migrated_events: migratedEvents.length,
      boundaries: {
        paused_at: pausedAt,
        verified_at: verifiedAt,
        switched_at: switchedAt,
        resumed_at: pausedAt,
      },
      verify,
    }
    return report
  } finally {
    await params.resume_tenant(params.tenant_id)
    if (report) {
      report.boundaries.resumed_at = Date.now()
    }
  }
}
