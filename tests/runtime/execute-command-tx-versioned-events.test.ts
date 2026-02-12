import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { executeCommandTx } from "../../runtime/execute-command-tx"
import type { CoreIrV0 } from "../../core/ir/types"
import type { VmIntrinsics } from "../../core/vm/eval"

describe("versioned event table routing", () => {
  it("writes to events_vN/snapshots_vN for active tenant version", async () => {
    const sqlLog: string[] = []

    const adapter = {
      async get_active_version (_tenant_id: string): Promise<number> {
        return 2
      },
      async tx<T> (fn: (tx: { exec: (sql: string, binds?: any[]) => Promise<{ rows?: any[] }> }) => Promise<T>): Promise<T> {
        const tx = {
          async exec (sql: string, _binds: any[] = []): Promise<{ rows?: any[] }> {
            sqlLog.push(sql)

            if (sql.includes("SELECT result_json FROM command_receipts")) return { rows: [] }
            if (sql.includes("SELECT ts FROM command_receipts")) return { rows: [] }
            if (sql.includes("SELECT active_version FROM tenant_versions")) return { rows: [{ active_version: 2 }] }

            if (sql.includes("FROM snapshots_v2") && sql.includes("LIMIT 1")) {
              return { rows: [{ state: "new", attrs_json: "{}", updated_ts: 1, severity_i: null, created_at: null }] }
            }
            if (sql.includes("SELECT COALESCE(MAX(seq), 0) AS max_seq") && sql.includes("FROM events_v2")) {
              return { rows: [{ max_seq: 0 }] }
            }
            if (sql.includes("INSERT INTO events_v2")) return { rows: [] }
            if (sql.includes("INSERT INTO snapshots_v2")) return { rows: [] }
            if (sql.includes("INSERT INTO command_receipts")) return { rows: [] }
            if (sql.includes("FROM sla_status")) return { rows: [] }
            if (sql.includes("SELECT *") && sql.includes("FROM snapshots_v2")) return { rows: [] }

            throw new Error(`unexpected SQL: ${sql}`)
          },
        }
        return fn(tx)
      },
    }

    const ir: CoreIrV0 = {
      version: 0,
      types: {
        Ticket: {
          id_type: "string",
          states: ["new", "done"],
          initial_state: "new",
          attrs: {},
          commands: {
            close: {
              input: {},
              guard: { expr: { lit: { bool: true } } as any },
              emits: [{ event_type: "closed", payload: {} }],
            },
          },
          reducer: {
            closed: [{ set_state: { expr: { lit: { string: "done" } } as any } }],
          },
        },
      },
    }

    const intrinsics: VmIntrinsics = {
      has_role: () => true,
      role_of: () => "user",
      auth_ok: () => true,
      constraint: () => true,
      len: (v: any) => (Array.isArray(v) ? v.length : typeof v === "string" ? v.length : v && typeof v === "object" ? Object.keys(v).length : 0),
      str: (v: any) => (v === null ? null : String(v)),
      int: (v: any) => (typeof v === "number" ? Math.trunc(v) : null),
      float: (v: any) => (typeof v === "number" ? v : null),
    }

    const out = await executeCommandTx({
      ir,
      store: { adapter: adapter as any },
      intrinsics,
      req: {
        tenant_id: "t",
        actor_id: "u",
        command_id: "c1",
        entity_type: "Ticket",
        entity_id: "e1",
        command_name: "close",
        input: {},
        now: 10,
      },
    })

    assert.equal(out.seq_from, 1)
    assert.ok(sqlLog.some((s) => s.includes("events_v2")))
    assert.ok(sqlLog.some((s) => s.includes("snapshots_v2")))
  })
})
