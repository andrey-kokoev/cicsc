import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { executeCommandTx } from "../../runtime/execute-command-tx"
import type { CoreIrV0 } from "../../core/ir/types"
import type { VmIntrinsics } from "../../core/vm/eval"

type EventRec = {
  tenant_id: string
  entity_type: string
  entity_id: string
  seq: number
  event_type: string
  payload_json: string
  ts: number
  actor_id: string
  command_id: string
}

type SnapshotRec = {
  tenant_id: string
  entity_type: string
  entity_id: string
  state: string
  attrs_json: string
  updated_ts: number
  severity_i: number | null
  created_at: number | null
}

type MemState = {
  events: EventRec[]
  snapshots: Map<string, SnapshotRec>
  receipts: Map<string, string>
}

function skey (tenant_id: string, entity_type: string, entity_id: string): string {
  return `${tenant_id}|${entity_type}|${entity_id}`
}

function rkey (tenant_id: string, command_id: string): string {
  return `${tenant_id}|${command_id}`
}

function cloneState (s: MemState): MemState {
  return {
    events: s.events.map((e) => ({ ...e })),
    snapshots: new Map(Array.from(s.snapshots.entries(), ([k, v]) => [k, { ...v }])),
    receipts: new Map(s.receipts),
  }
}

function makeTxAdapter (initial: MemState) {
  let committed = cloneState(initial)

  const adapter = {
    async get_active_version (_tenant_id: string): Promise<number> {
      return 0
    },
    async tx<T> (fn: (tx: { exec: (sql: string, binds?: any[]) => Promise<{ rows?: any[] }> }) => Promise<T>): Promise<T> {
      const working = cloneState(committed)
      const tx = {
        async exec (sql: string, binds: any[] = []): Promise<{ rows?: any[] }> {
          if (sql.includes("SELECT result_json FROM command_receipts")) {
            const row = working.receipts.get(rkey(String(binds[0]), String(binds[1])))
            return { rows: row ? [{ result_json: row }] : [] }
          }

          if (sql.includes("SELECT state, attrs_json, updated_ts, severity_i, created_at")) {
            const row = working.snapshots.get(skey(String(binds[0]), String(binds[1]), String(binds[2])))
            if (!row) return { rows: [] }
            return {
              rows: [{
                state: row.state,
                attrs_json: row.attrs_json,
                updated_ts: row.updated_ts,
                severity_i: row.severity_i,
                created_at: row.created_at,
              }],
            }
          }

          if (sql.includes("SELECT COALESCE(MAX(seq), 0) AS max_seq")) {
            const [tenant_id, entity_type, entity_id] = binds.map(String)
            const max = working.events
              .filter((e) => e.tenant_id === tenant_id && e.entity_type === entity_type && e.entity_id === entity_id)
              .reduce((m, e) => (e.seq > m ? e.seq : m), 0)
            return { rows: [{ max_seq: max }] }
          }

          if (sql.includes("SELECT *") && sql.includes("FROM snapshots_v0")) {
            const [tenant_id, entity_type] = binds.map(String)
            const rows = Array.from(working.snapshots.values()).filter(
              (s) => s.tenant_id === tenant_id && s.entity_type === entity_type
            )
            return { rows }
          }

          if (sql.includes("INSERT INTO events_v0")) {
            for (let i = 0; i < binds.length; i += 9) {
              working.events.push({
                tenant_id: String(binds[i + 0]),
                entity_type: String(binds[i + 1]),
                entity_id: String(binds[i + 2]),
                seq: Number(binds[i + 3]),
                event_type: String(binds[i + 4]),
                payload_json: String(binds[i + 5]),
                ts: Number(binds[i + 6]),
                actor_id: String(binds[i + 7]),
                command_id: String(binds[i + 8]),
              })
            }
            return { rows: [] }
          }

          if (sql.includes("INSERT INTO snapshots_v0")) {
            const [tenant_id, entity_type, entity_id, state, attrs_json, updated_ts, severity_i, created_at] = binds
            working.snapshots.set(skey(String(tenant_id), String(entity_type), String(entity_id)), {
              tenant_id: String(tenant_id),
              entity_type: String(entity_type),
              entity_id: String(entity_id),
              state: String(state),
              attrs_json: String(attrs_json),
              updated_ts: Number(updated_ts),
              severity_i: severity_i == null ? null : Number(severity_i),
              created_at: created_at == null ? null : Number(created_at),
            })
            return { rows: [] }
          }

          if (sql.includes("INSERT INTO command_receipts")) {
            const [tenant_id, command_id, _entity_type, _entity_id, result_json] = binds
            const key = rkey(String(tenant_id), String(command_id))
            if (!working.receipts.has(key)) working.receipts.set(key, String(result_json))
            return { rows: [] }
          }

          throw new Error(`Unhandled SQL in test adapter: ${sql}`)
        },
      }

      try {
        const out = await fn(tx)
        committed = working
        return out
      } catch (e) {
        throw e
      }
    },
  }

  return {
    adapter,
    getCommitted: () => committed,
  }
}

const ir: CoreIrV0 = {
  version: 0,
  types: {
    Ticket: {
      id_type: "string",
      states: ["new", "done", "forbidden"],
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
  constraints: {
    no_forbidden_rows: {
      kind: "snapshot",
      on_type: "Ticket",
      expr: { ne: [{ var: { row: { field: "state" } } }, { lit: { string: "forbidden" } }] } as any,
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

describe("snapshot constraints in tx scope", () => {
  it("rejects command when another row of the constrained type violates snapshot constraint", async () => {
    const init: MemState = {
      events: [],
      snapshots: new Map([
        [
          skey("t", "Ticket", "e1"),
          {
            tenant_id: "t",
            entity_type: "Ticket",
            entity_id: "e1",
            state: "new",
            attrs_json: "{}",
            updated_ts: 1,
            severity_i: null,
            created_at: null,
          },
        ],
        [
          skey("t", "Ticket", "e2"),
          {
            tenant_id: "t",
            entity_type: "Ticket",
            entity_id: "e2",
            state: "forbidden",
            attrs_json: "{}",
            updated_ts: 1,
            severity_i: null,
            created_at: null,
          },
        ],
      ]),
      receipts: new Map(),
    }

    const mocked = makeTxAdapter(init)
    const store = { adapter: mocked.adapter as any }

    await assert.rejects(async () => {
      await executeCommandTx({
        ir,
        store,
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
    }, /constraint violated: no_forbidden_rows/)

    const committed = mocked.getCommitted()
    assert.equal(committed.events.length, 0)
    assert.equal(committed.snapshots.get(skey("t", "Ticket", "e1"))?.state, "new")
  })

  it("accepts command when all rows satisfy the constrained snapshot invariant", async () => {
    const init: MemState = {
      events: [],
      snapshots: new Map([
        [
          skey("t", "Ticket", "e1"),
          {
            tenant_id: "t",
            entity_type: "Ticket",
            entity_id: "e1",
            state: "new",
            attrs_json: "{}",
            updated_ts: 1,
            severity_i: null,
            created_at: null,
          },
        ],
        [
          skey("t", "Ticket", "e2"),
          {
            tenant_id: "t",
            entity_type: "Ticket",
            entity_id: "e2",
            state: "done",
            attrs_json: "{}",
            updated_ts: 1,
            severity_i: null,
            created_at: null,
          },
        ],
      ]),
      receipts: new Map(),
    }

    const mocked = makeTxAdapter(init)
    const store = { adapter: mocked.adapter as any }

    const result = await executeCommandTx({
      ir,
      store,
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

    assert.equal(result.seq_from, 1)
    assert.equal(result.seq_to, 1)
    assert.equal(result.state, "done")
  })
})
