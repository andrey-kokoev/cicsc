// tests/runtime/workflow/integration.test.ts

import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { WorkflowManager } from "../../../runtime/workflow/manager"
import { WorkflowWorker } from "../../../runtime/workflow/worker"
import { SqliteD1Adapter } from "../../../adapters/sqlite/src/adapter"
import type { CoreIrV0 } from "../../../core/ir/types"

function makeMemoryD1 () {
  const tables = new Map<string, any[]>()

  return {
    tables,
    prepare (sql: string) {
      return {
        bind (...binds: any[]) {
          return {
            sql,
            binds,
            async all () {
              if (sql.includes("FROM workflow_instances")) {
                let results = tables.get("workflow_instances") || []
                if (sql.includes("next_run_at <= ?") || sql.includes("status = 'running'")) {
                  const tenant_id = binds[0]
                  const now = binds[1]
                  // Simplified filter
                  results = results.filter(r => r.tenant_id === tenant_id && (r.status === 'running' || (r.status === 'waiting' && r.next_run_at <= now)))
                } else if (sql.includes("status = 'waiting' AND wait_event_type = ?")) {
                  const tenant_id = binds[0]
                  const event_type = binds[1]
                  results = results.filter(r => r.tenant_id === tenant_id && r.status === 'waiting' && r.wait_event_type === event_type)
                }
                return { results }
              }
              return { results: [] }
            },
            async first () {
              if (sql.includes("FROM workflow_instances")) {
                const results = tables.get("workflow_instances") || []
                const workflow_id = binds[1]
                return results.find(r => r.workflow_id === workflow_id) || null
              }
              return null
            },
            async run () {
              if (sql.includes("INSERT INTO workflow_instances")) {
                const table = tables.get("workflow_instances") || []
                table.push({
                  tenant_id: binds[0], workflow_id: binds[1], workflow_name: binds[2],
                  current_step: binds[3], status: binds[4], wait_event_type: binds[5],
                  context_json: binds[6], history_json: binds[7], next_run_at: binds[8],
                  created_ts: binds[9], updated_ts: binds[10]
                })
                tables.set("workflow_instances", table)
              }
              if (sql.includes("UPDATE workflow_instances")) {
                const table = tables.get("workflow_instances") || []
                const workflow_id = binds[binds.length - 1]
                const inst = table.find(r => r.workflow_id === workflow_id)
                if (inst) {
                  const setPart = sql.split("SET")[1].split("WHERE")[0]
                  const assignments = setPart.split(",").map(part => part.trim().split("=")[0].trim())
                  assignments.forEach((field, idx) => {
                    (inst as any)[field] = binds[idx]
                  })
                }
              }
              if (sql.includes("INSERT INTO workflow_log")) {
                const table = tables.get("workflow_log") || []
                table.push({
                  tenant_id: binds[0], workflow_id: binds[1], step_name: binds[2],
                  action: binds[3], payload_json: binds[4], ts: binds[5]
                })
                tables.set("workflow_log", table)
              }
              return { success: true, meta: { changes: 1 } }
            }
          }
        }
      }
    },
    async batch () { return [] }
  }
}

describe("Workflow Integration", () => {
  const ir: CoreIrV0 = {
    version: "0",
    types: {
      Ticket: {
        initial_state: "open",
        commands: {
          Close: { guard: { expr: { lit: true } }, emits: [{ event_type: "Closed", payload: {} }] }
        },
        shadows: {},
        attrs: {},
        reducer: {}
      }
    },
    workflows: {
      AutoClose: {
        initial_step: "check_status",
        on_event: "Created",
        steps: {
          check_status: {
            kind: "decision",
            cases: [
              {
                condition: {
                  eq: [
                    { get: { expr: { var: { arg: { name: "trigger_event" } } }, path: "payload.priority" } },
                    { lit: { string: "high" } },
                  ],
                },
                next: "wait_long",
              },
            ],
            default_next: "close_it",
          },
          close_it: {
            kind: "command",
            entity_type: "Ticket",
            command: "Close",
            input_map: {
              entity_id: { get: { expr: { var: { arg: { name: "trigger_event" } } }, path: "payload.id" } },
            },
            next: "end",
          },
          wait_long: {
            kind: "wait",
            event_type: "UserAction",
            timeout_seconds: 3600,
            next: "close_it",
          },
          end: { kind: "end" },
        },
      },
    },
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

  it("triggers a workflow on event", async () => {
    const db = makeMemoryD1()
    const adapter = new SqliteD1Adapter(db as any)
    const manager = new WorkflowManager(ir, adapter)

    await manager.onEventsEmitted({
      tenant_id: "t1",
      entity_type: "Ticket",
      entity_id: "e1",
      events: [{ event_type: "Created", payload: { id: "e1", priority: "low" }, ts: 1000, actor_id: "u1" }]
    })

    const instances = db.tables.get("workflow_instances") || []
    assert.equal(instances.length, 1)
    assert.equal(instances[0].workflow_name, "AutoClose")
    assert.equal(instances[0].status, "running")
  })

  it("worker executes sequential steps", async () => {
    const db = makeMemoryD1()
    const adapter = new SqliteD1Adapter(db as any)
    const store: any = adapter // it implements the needed methods

    // Manually create an instance
    await adapter.create_workflow_instance({
      tenant_id: "t1",
      workflow_id: "wf1",
      workflow_name: "AutoClose",
      current_step: "check_status",
      status: "running",
      wait_event_type: null,
      context_json: JSON.stringify({ trigger_event: { payload: { id: "e1", priority: "low" } } }),
      history_json: "[]",
      next_run_at: null,
      created_ts: 1000,
      updated_ts: 1000
    })

    const runCommand = async (tid: string, type: string, id: string, cmd: string, input: any) => {
      return { success: true }
    }

    const worker = new WorkflowWorker(ir, store, intrinsics as any, runCommand)
    await worker.pollAndExecute("t1", { now: 2000 })

    const inst = await adapter.get_workflow_instance("t1", "wf1")
    assert.equal(inst.status, "completed")
    assert.equal(inst.current_step, "end")

    const logs = db.tables.get("workflow_log") || []
    // check_status (decision -> next: close_it)
    // close_it (command -> next: end)
    // end (action: end)
    assert.ok(logs.length >= 2)
  })

  it("worker handles wait steps (timeout)", async () => {
    const db = makeMemoryD1()
    const adapter = new SqliteD1Adapter(db as any)
    const store: any = adapter

    await adapter.create_workflow_instance({
      tenant_id: "t1",
      workflow_id: "wf2",
      workflow_name: "AutoClose",
      current_step: "wait_long",
      status: "running",
      wait_event_type: null,
      context_json: JSON.stringify({ trigger_event: { payload: { id: "e1", priority: "high" } } }),
      history_json: "[]",
      next_run_at: null,
      created_ts: 1000,
      updated_ts: 1000
    })

    const worker = new WorkflowWorker(ir, store, intrinsics as any, async () => ({}))

    // First poll starts the wait
    await worker.pollAndExecute("t1", { now: 2000 })

    let inst = await adapter.get_workflow_instance("t1", "wf2")
    assert.equal(inst.status, "waiting")
    assert.notEqual(inst.next_run_at, null)
    assert.equal(inst.next_run_at, 2000 + 3600)

    // Second poll before timeout should do nothing (listDue will exclude it)
    await worker.pollAndExecute("t1", { now: 3000 })
    inst = await adapter.get_workflow_instance("t1", "wf2")
    assert.equal(inst.status, "waiting")
    assert.equal(inst.current_step, "wait_long")

    // Third poll after timeout
    await worker.pollAndExecute("t1", { now: 10000 })
    inst = await adapter.get_workflow_instance("t1", "wf2")
    // After timeout, it should go to next: close_it, then end
    assert.equal(inst.status, "completed")
  })

  it("manager wakes up waiting workflow on event", async () => {
    const db = makeMemoryD1()
    const adapter = new SqliteD1Adapter(db as any)
    const manager = new WorkflowManager(ir, adapter)

    await adapter.create_workflow_instance({
      tenant_id: "t1",
      workflow_id: "wf3",
      workflow_name: "AutoClose",
      current_step: "wait_long",
      status: "waiting",
      wait_event_type: "UserAction",
      context_json: JSON.stringify({ trigger_event: { payload: { id: "e1", priority: "high" } } }),
      history_json: "[]",
      next_run_at: 5000,
      created_ts: 1000,
      updated_ts: 1000,
    })

    await manager.onEventsEmitted({
      tenant_id: "t1",
      entity_type: "User",
      entity_id: "u1",
      events: [{ event_type: "UserAction", payload: { action: "cancel" }, ts: 3000, actor_id: "u1" }],
    })

    const inst = await adapter.get_workflow_instance("t1", "wf3")
    assert.equal(inst.status, "running")
    assert.equal(inst.current_step, "close_it")
    assert.equal(inst.wait_event_type, null)

    const context = JSON.parse(inst.context_json)
    assert.deepEqual(context.wait_long, { action: "cancel" })
  })

  it("executes compensation on failure (Saga)", async () => {
    const db = makeMemoryD1()
    const adapter = new SqliteD1Adapter(db as any)
    const store: any = adapter

    const sagaIr: CoreIrV0 = {
      ...ir,
      workflows: {
        Booking: {
          initial_step: "book_flight",
          steps: {
            book_flight: {
              kind: "command",
              entity_type: "Flight",
              command: "Book",
              input_map: { id: { lit: { string: "f1" } } },
              next: "book_hotel",
              compensate: {
                kind: "command",
                entity_type: "Flight",
                command: "Cancel",
                input_map: { id: { lit: { string: "f1" } } },
              },
            },
            book_hotel: {
              kind: "command",
              entity_type: "Hotel",
              command: "Reserve",
              input_map: { id: { lit: { string: "h1" } } },
              next: "end",
            },
            end: { kind: "end" },
          },
        },
      },
    }

    const commands: string[] = []
    const runCommand = async (tid: string, type: string, id: string, cmd: string, input: any) => {
      commands.push(`${type}.${cmd}`)
      if (type === "Hotel" && cmd === "Reserve") {
        throw new Error("Hotel full")
      }
      return { success: true }
    }

    await adapter.create_workflow_instance({
      tenant_id: "t1",
      workflow_id: "wf4",
      workflow_name: "Booking",
      current_step: "book_flight",
      status: "running",
      wait_event_type: null,
      context_json: "{}",
      history_json: "[]",
      next_run_at: null,
      created_ts: 1000,
      updated_ts: 1000,
    })

    const worker = new WorkflowWorker(sagaIr, store, intrinsics as any, runCommand)
    await worker.pollAndExecute("t1", { now: 2000 })

    const inst = await adapter.get_workflow_instance("t1", "wf4")
    assert.equal(inst.status, "compensated")

    // Commands should be: Flight.Book, Hotel.Reserve (fails), Flight.Cancel
    assert.deepEqual(commands, ["Flight.Book", "Hotel.Reserve", "Flight.Cancel"])
  })
})
