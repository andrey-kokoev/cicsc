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

type SlaRec = {
  tenant_id: string
  name: string
  entity_type: string
  entity_id: string
  start_ts: number | null
  stop_ts: number | null
  deadline_ts: number | null
  breached: 0 | 1
  updated_ts: number
}

type MemState = {
  events: EventRec[]
  snapshots: Map<string, SnapshotRec>
  receipts: Map<string, string>
  slas: SlaRec[]
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
    slas: s.slas.map((x) => ({ ...x })),
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

          if (sql.includes("SELECT active_version FROM tenant_versions")) {
            return { rows: [{ active_version: 0 }] }
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

          if (sql.includes("FROM sla_status")) {
            const [tenant_id, name, entity_type, entity_id, now] = binds
            const due = working.slas.find((s) =>
              s.tenant_id === tenant_id &&
              s.name === name &&
              s.entity_type === entity_type &&
              s.entity_id === entity_id &&
              s.breached === 0 &&
              s.stop_ts == null &&
              s.deadline_ts != null &&
              s.deadline_ts < now
            )
            return { rows: due ? [{ due: 1 }] : [] }
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
  slas: {
    response_time: {
      name: "response_time",
      on_type: "Ticket",
      start: { event: { name: "created" } },
      stop: { event: { name: "closed" } },
      within_seconds: 3600,
      enforce: { none: true },
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

describe("SLA enforcement in tx", () => {
  it("rejects command when entity has overdue active SLA", async () => {
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
      ]),
      receipts: new Map(),
      slas: [
        {
          tenant_id: "t",
          name: "response_time",
          entity_type: "Ticket",
          entity_id: "e1",
          start_ts: 1,
          stop_ts: null,
          deadline_ts: 5,
          breached: 0,
          updated_ts: 1,
        },
      ],
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
    }, /sla violated: response_time/)

    const committed = mocked.getCommitted()
    assert.equal(committed.events.length, 0)
    assert.equal(committed.snapshots.get(skey("t", "Ticket", "e1"))?.state, "new")
  })

  it("accepts command when SLA is not overdue", async () => {
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
      ]),
      receipts: new Map(),
      slas: [
        {
          tenant_id: "t",
          name: "response_time",
          entity_type: "Ticket",
          entity_id: "e1",
          start_ts: 1,
          stop_ts: null,
          deadline_ts: 100,
          breached: 0,
          updated_ts: 1,
        },
      ],
    }

    const mocked = makeTxAdapter(init)
    const store = { adapter: mocked.adapter as any }

    const out = await executeCommandTx({
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

    assert.equal(out.state, "done")
    assert.equal(out.seq_from, 1)
    assert.equal(out.seq_to, 1)
  })
})
