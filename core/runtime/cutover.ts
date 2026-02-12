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
  await params.pause_tenant(params.tenant_id)

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
      return {
        ok: false,
        mode: "pause_migrate_resume",
        migration_id: params.migration_id,
        from_version: verify.from_version,
        to_version: verify.to_version,
        migrated_events: 0,
        verify,
        error: verify.error ?? "migration replay verification failed",
      }
    }

    const migration = (params.to_bundle as any)?.core_ir?.migrations?.[params.migration_id]
    const migratedEvents = transformHistoryWithMigration({
      migration,
      events: sourceEvents,
      intrinsics: params.intrinsics,
      policies: params.policies,
    })

    await params.write_target_history(migratedEvents)
    await params.set_active_version(params.tenant_id, verify.to_version)

    return {
      ok: true,
      mode: "pause_migrate_resume",
      migration_id: params.migration_id,
      from_version: verify.from_version,
      to_version: verify.to_version,
      migrated_events: migratedEvents.length,
      verify,
    }
  } finally {
    await params.resume_tenant(params.tenant_id)
  }
}
