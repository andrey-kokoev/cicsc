// runtime/schedule/worker.ts

import type { CoreIrV0 } from "../../core/ir/types"
import type { ScheduledJob } from "../db/schedule-store"
import { executeCommand } from "../execute-command"
import { evalExpr, type VmIntrinsics } from "../../core/vm/eval"
import type { D1Store } from "../db/d1-store"
import * as parser from "cron-parser"

export class ScheduleWorker {
  constructor(
    private store: D1Store,
    private ir: CoreIrV0,
    private intrinsics: VmIntrinsics
  ) {}

  /**
   * Main polling loop entry point.
   */
  async pollAndExecute(tenant_id: string, options: { now?: number; batchSize?: number } = {}) {
    const now = options.now ?? Date.now()
    const batchSize = options.batchSize ?? 10
    
    // 1. Sync CRON schedules from IR
    await this.syncCronSchedules(tenant_id, now)
    
    // 2. Process CRON triggers to populate pending jobs
    await this.processCronTriggers(tenant_id, now)

    // 3. Execute due jobs
    const dueJobs = await this.store.listDueJobs(tenant_id, now, batchSize)
    
    let processed = 0
    let errors = 0

    for (const job of dueJobs) {
      const ok = await this.store.markExecuting(tenant_id, job.id, now)
      if (!ok) continue

      try {
        await this.executeJob(tenant_id, job)
        await this.store.completeJob(tenant_id, job.id, Date.now())
        processed++
      } catch (err: any) {
        errors++
        console.error(`[ScheduleWorker] Job ${job.id} failed:`, err)
        
        const spec = this.ir.schedules?.[job.schedule_name]
        const retryLimit = spec?.execution?.retry?.max_attempts ?? 3
        const backoff = spec?.execution?.retry?.backoff_ms ?? 300000
        
        const nextRetryAt = job.attempts < retryLimit ? Date.now() + backoff : undefined
        await this.store.failJob(tenant_id, job.id, String(err), nextRetryAt)
      }
    }

    return { processed, errors }
  }

  private async syncCronSchedules(tenant_id: string, now: number) {
    for (const [name, spec] of Object.entries(this.ir.schedules ?? {})) {
      if (spec.trigger && 'cron' in spec.trigger) {
        const cronExpr = spec.trigger.cron
        
        // Simple sync: only upsert if we don't have it or it changed.
        // For now, just trust adapter's upsert as a baseline.
        // In a real system, we'd check current DB state first to avoid resetting next_run_at.
        
        try {
          const interval = parser.CronExpressionParser.parse(cronExpr, { 
            currentDate: new Date(now - 1),
            tz: spec.execution?.timezone || 'UTC'
          })
          const nextRunAt = interval.next().getTime()
          
          await this.store.upsertCronSchedule({
            tenant_id,
            name,
            expression: cronExpr,
            timezone: spec.execution?.timezone || 'UTC',
            next_run_at: nextRunAt
          })
        } catch (e) {
          console.error(`Invalid cron expression for ${name}: ${cronExpr}`, e)
        }
      }
    }
  }

  private async processCronTriggers(tenant_id: string, now: number) {
    const dueCrons = await this.store.listDueCronSchedules({ tenant_id, now })
    for (const cron of dueCrons) {
       const spec = this.ir.schedules?.[cron.name]
       if (!spec) continue
       
       // Schedule the job for this occurrence
       const inputMap: Record<string, any> = {}
       for (const [k, ex] of Object.entries(spec.action.input_map)) {
         inputMap[k] = evalExpr(ex, {
            now: cron.next_run_at, // Evaluate at the time it was supposed to run
            actor: "system:scheduler",
            state: "",
            input: {},
            attrs: {},
            row: {},
            arg: {},
            intrinsics: this.intrinsics
         })
       }

       await this.store.scheduleJob(tenant_id, {
         schedule_name: cron.name,
         trigger_type: "cron",
         scheduled_at: cron.next_run_at,
         command_entity: spec.action.entity_type,
         command_name: spec.action.command,
         input_json: JSON.stringify(inputMap),
         queue_name: spec.queue,
         timezone: cron.timezone
       })

       // Advance to next occurrence
       const interval = parser.CronExpressionParser.parse(cron.expression, {
         currentDate: new Date(cron.next_run_at + 1),
         tz: cron.timezone || 'UTC'
       })
       const nextRunAt = interval.next().getTime()
       await this.store.updateCronLastRun({
          tenant_id,
          name: cron.name,
          last_run_at: cron.next_run_at,
          next_run_at: nextRunAt
       })
    }
  }

  private async executeJob(tenant_id: string, job: ScheduledJob) {
    const spec = this.ir.schedules?.[job.schedule_name]
    if (!spec) throw new Error(`unknown schedule spec: ${job.schedule_name}`)

    const input: Record<string, any> = JSON.parse(job.input_json)

    if (spec.queue) {
      // Route through queue
      await this.store.enqueue({
        tenant_id,
        queue_name: spec.queue,
        message: {
          schedule_name: job.schedule_name,
          job_id: job.id,
          entity_type: job.command_entity,
          entity_id: job.entity_id,
          command: job.command_name,
          input,
        },
        idempotency_key: `schedule:${job.id}:${job.attempts}`
      })
      return
    }

    await executeCommand({
      ir: this.ir,
      store: this.store,
      intrinsics: this.intrinsics,
      req: {
        tenant_id,
        actor_id: "system:scheduler",
        command_id: `schedule:${job.id}:${job.attempts}`,
        entity_type: job.command_entity,
        entity_id: job.entity_id || "global", // Default to global if no entity_id
        command_name: job.command_name,
        input: input,
        now: Math.floor(Date.now() / 1000),
      },
    })
  }
}
