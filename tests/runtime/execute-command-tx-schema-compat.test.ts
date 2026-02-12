import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { executeCommandTx } from "../../runtime/execute-command-tx"
import type { CoreIrV0 } from "../../core/ir/types"
import type { VmIntrinsics } from "../../core/vm/eval"

describe("schema compatibility checks", () => {
  it("fails fast when active version tables are missing", async () => {
    const adapter = {
      async get_active_version (_tenant_id: string): Promise<number> {
        return 2
      },
      async tx<T> (fn: (tx: { exec: (sql: string, binds?: any[]) => Promise<{ rows?: any[] }> }) => Promise<T>): Promise<T> {
        const tx = {
          async exec (sql: string, _binds: any[] = []): Promise<{ rows?: any[] }> {
            if (sql.includes("SELECT result_json FROM command_receipts")) return { rows: [] }
            if (sql.includes("SELECT active_version FROM tenant_versions")) return { rows: [{ active_version: 2 }] }
            if (sql.includes("SELECT 1 FROM events_v2")) throw new Error("no such table: events_v2")
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
          states: ["new"],
          initial_state: "new",
          attrs: {},
          commands: {
            c: { input: {}, guard: { expr: { lit: { bool: true } } as any }, emits: [] },
          },
          reducer: {},
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

    await assert.rejects(async () => {
      await executeCommandTx({
        ir,
        store: { adapter: adapter as any },
        intrinsics,
        req: {
          tenant_id: "t",
          actor_id: "u",
          command_id: "c1",
          entity_type: "Ticket",
          entity_id: "e1",
          command_name: "c",
          input: {},
          now: 10,
        },
      })
    }, /schema incompatible for active_version=2/)
  })
})
