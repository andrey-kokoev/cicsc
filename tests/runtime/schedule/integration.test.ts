// tests/runtime/schedule/integration.test.ts

import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { ScheduleManager } from "../../../runtime/schedule/manager"
import { ScheduleWorker } from "../../../runtime/schedule/worker"
import { makeD1Store } from "../../../runtime/db/d1-store"
import { SqliteD1Adapter } from "../../../adapters/sqlite/src/adapter"
import type { CoreIrV0 } from "../../../core/ir/types"

// A smart fake D1 for testing scheduling logic
function makeMemoryD1() {
  const tables = new Map<string, any[]>()
  
  return {
    tables,
    prepare(sql: string) {
      return {
        bind(...binds: any[]) {
          return {
            sql,
            binds,
            async all() {
              if (sql.includes("FROM scheduled_jobs")) {
                let results = tables.get("scheduled_jobs") || []
                if (sql.includes("scheduled_at <= ?")) {
                  const tenant_id = binds[0]
                  const now = binds[2]
                  results = results.filter(r => r.tenant_id === tenant_id && (r.status === 'pending' || r.status === 'failed') && r.scheduled_at <= now)
                }
                return { results }
              }
              if (sql.includes("FROM cron_schedules")) {
                let results = tables.get("cron_schedules") || []
                if (sql.includes("next_run_at <= ?")) {
                  const tenant_id = binds[0]
                  const now = binds[1]
                  results = results.filter(r => r.tenant_id === tenant_id && r.next_run_at <= now)
                }
                return { results }
              }
              return { results: [] }
            },
            async first() {
              if (sql.includes("FROM snapshots_v0")) return null
              if (sql.includes("active_version")) return { active_version: 0 }
              return null
            }
          }
        }
      }
    },
    async batch(stmts: any[]) {
      const results: any[] = []
      for (const s of stmts) {
        const sql = s.sql
        const binds = s.binds || []
        
        if (sql.includes("INSERT INTO scheduled_jobs")) {
          const table = tables.get("scheduled_jobs") || []
          table.push({
            tenant_id: binds[0],
            id: binds[1],
            schedule_name: binds[2],
            trigger_type: binds[3],
            entity_type: binds[4],
            entity_id: binds[5],
            event_type: binds[6],
            scheduled_at: binds[7],
            timezone: binds[8],
            command_entity: binds[9],
            command_name: binds[10],
            input_json: binds[11],
            queue_name: binds[12],
            status: binds[13],
            attempts: binds[14],
            created_at: binds[15],
            updated_at: binds[16]
          })
          tables.set("scheduled_jobs", table)
          results.push({ success: true, meta: { changes: 1 } })
          continue
        }

        if (sql.includes("INSERT INTO cron_schedules")) {
          const table = tables.get("cron_schedules") || []
          const existing = table.find(r => r.tenant_id === binds[0] && r.name === binds[1])
          if (existing) {
             existing.expression = binds[2]
             existing.next_run_at = binds[4]
          } else {
            table.push({
              tenant_id: binds[0],
              name: binds[1],
              expression: binds[2],
              timezone: binds[3],
              next_run_at: binds[4]
            })
          }
          tables.set("cron_schedules", table)
          results.push({ success: true, meta: { changes: 1 } })
          continue
        }

        if (sql.includes("UPDATE cron_schedules")) {
           const table = tables.get("cron_schedules") || []
           const cron = table.find(r => r.tenant_id === binds[2] && r.name === binds[3])
           if (cron) {
             cron.last_run_at = binds[0]
             cron.next_run_at = binds[1]
             results.push({ success: true, meta: { changes: 1 } })
           } else {
             results.push({ success: true, meta: { changes: 0 } })
           }
           continue
        }

        if (sql.includes("UPDATE scheduled_jobs SET status='executing'")) {
            const table = tables.get("scheduled_jobs") || []
            const job = table.find(j => j.id === binds[2] && j.tenant_id === binds[1])
            if (job) {
                job.status = 'executing'
                job.attempts++
                results.push({ success: true, meta: { changes: 1 } })
            } else {
                results.push({ success: true, meta: { changes: 0 } })
            }
            continue
        }

        if (sql.includes("UPDATE scheduled_jobs SET status='completed'")) {
            const table = tables.get("scheduled_jobs") || []
            const job = table.find(j => j.id === binds[1] && j.tenant_id === binds[0])
            if (job) {
                job.status = 'completed'
                results.push({ success: true, meta: { changes: 1 } })
            } else {
                results.push({ success: true, meta: { changes: 0 } })
            }
            continue
        }

        results.push({ success: true, meta: { changes: 0 } })
      }
      return results
    },
    async exec(sql: string) {
       return { count: 0, duration: 0 }
    }
  }
}

describe("Schedule Integration", () => {
  const ir: CoreIrV0 = {
    version: "0",
    types: {
      Ticket: {
        initial_state: "open",
        commands: {
          Create: {
            guard: { expr: { literal: true } },
            emits: [{ event_type: "Created", payload: {} }]
          },
          Remind: {
            guard: { expr: { literal: true } },
            emits: []
          }
        },
        shadows: {}
      }
    },
    schedules: {
      FollowUp: {
        trigger: { on_event: "Created", delay_seconds: 60 },
        action: {
          entity_type: "Ticket",
          command: "Remind",
          input_map: { msg: { literal: "hello" } }
        },
        queue: "default"
      }
    }
  }

  const intrinsics = {
    auth_ok: () => true,
    role_of: () => "admin",
    has_role: () => true,
    constraint: () => true,
    len: (v: any) => v.length,
    str: (v: any) => String(v),
    int: (v: any) => parseInt(v),
    float: (v: any) => parseFloat(v)
  }

  it("schedules a job on event", async () => {
    const db = makeMemoryD1()
    const adapter = new SqliteD1Adapter(db as any)
    const store = makeD1Store({ adapter })
    const manager = new ScheduleManager(store, ir, intrinsics as any)

    await manager.onEventsEmitted({
      tenant_id: "t1",
      entity_type: "Ticket",
      entity_id: "e1",
      events: [{ event_type: "Created", payload: {}, ts: 1000, actor_id: "u1" }]
    })

    const jobs = db.tables.get("scheduled_jobs") || []
    assert.equal(jobs.length, 1)
    assert.equal(jobs[0]?.schedule_name, "FollowUp")
    assert.equal(jobs[0]?.scheduled_at, 1000 + 60 * 1000)
    assert.equal(jobs[0]?.status, "pending")
  })

  it("pollAndExecute executes the job", async () => {
    const db = makeMemoryD1()
    const adapter = new SqliteD1Adapter(db as any)
    const store = makeD1Store({ adapter })
    
    // Manually push a job
    await adapter.schedule_job({
        tenant_id: "t1",
        job: {
            schedule_name: "FollowUp",
            trigger_type: "event",
            entity_type: "Ticket",
            entity_id: "e1",
            event_type: "Created",
            scheduled_at: 1000,
            command_entity: "Ticket",
            command_name: "Remind",
            input_json: '{"msg":"hello"}'
        }
    })

    const worker = new ScheduleWorker(store, ir, intrinsics as any)
    
    const dueBefore = await adapter.list_due_jobs({ tenant_id: "t1", now: 5000 })
    assert.equal(dueBefore.length, 1, "Job should be due before poll")

    const result = await worker.pollAndExecute("t1", { now: 5000 })
    
    assert.equal(result.processed, 1, `Expected 1 job processed, got ${result.processed}. Errors: ${result.errors}`)
    
    // Check if job is completed
    const due = await adapter.list_due_jobs({ tenant_id: "t1", now: 5000 })
    assert.equal(due.length, 0)
  })

  it("CRON schedule generates jobs", async () => {
    const irCron: CoreIrV0 = {
      version: "0",
      types: {
         System: {
           initial_state: "ok",
           commands: { Tick: { guard: { expr: { literal: true } }, emits: [] } },
           shadows: {}
         }
      },
      schedules: {
        DailyTick: {
          trigger: { cron: "0 0 * * *" }, // Midnight every day
          action: { entity_type: "System", command: "Tick", input_map: {} }
        }
      }
    }
    const db = makeMemoryD1()
    const adapter = new SqliteD1Adapter(db as any)
    const store = makeD1Store({ adapter })
    const worker = new ScheduleWorker(store, irCron, intrinsics as any)

    // Poll at a time that triggers the cron
    const midnight = new Date("2026-01-01T00:00:00Z").getTime()
    await worker.pollAndExecute("t1", { now: midnight })

    // Check if a job was generated
    const allJobs = db.tables.get("scheduled_jobs") || []
    assert.equal(allJobs.length, 1, "Should have created 1 job")
    assert.equal(allJobs[0]?.schedule_name, "DailyTick")
    assert.equal(allJobs[0]?.trigger_type, "cron")

    // Check if next_run_at was advanced in cron_schedules
    const crons = await adapter.list_due_cron_schedules({ tenant_id: "t1", now: midnight + 1000 })
    assert.equal(crons.length, 0, "Cron should no longer be due")
  })
})
