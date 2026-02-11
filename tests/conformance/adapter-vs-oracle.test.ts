import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { interpretQuery } from "../../core/query/interpret"
import { evalExpr, type VmEnv } from "../../core/vm/eval"

// This file is a scaffold. It defines the oracle comparison shape.
// Hook it up to real adapters (D1, Postgres) once their SQL lowering emits {sql,binds}.
describe("conformance: adapter vs oracle", () => {
  it("oracle: Expr eval basic", () => {
    const env: VmEnv = {
      now: 1,
      actor: "u",
      state: "new",
      input: { title: "x" },
      attrs: { severity: "high" },
      row: {},
      arg: {},
      intrinsics: {
        has_role: () => false,
        role_of: () => "requester",
        auth_ok: () => true,
        constraint: () => true,
        len: (v) => (Array.isArray(v) ? v.length : typeof v === "string" ? v.length : v && typeof v === "object" ? Object.keys(v).length : 0),
        str: (v) => (v === null ? null : String(v)),
        int: (v) => (typeof v === "number" ? Math.trunc(v) : typeof v === "string" && v.trim() !== "" ? Number.parseInt(v, 10) : null),
        float: (v) => (typeof v === "number" ? v : typeof v === "string" && v.trim() !== "" ? Number.parseFloat(v) : null),
      },
    }

    const expr = { and: [{ eq: [{ var: { state: true } }, { lit: { string: "new" } }] }, { call: { fn: "auth_ok", args: [{ var: { actor: true } }, { lit: { string: "Ticket.create" } }] } }] } as any

    assert.equal(evalExpr(expr, env), true)
  })

  it("oracle: Query interpret filter/project/order", () => {
    const ctx = {
      now: 1,
      actor: "u",
      snap: (t: string) =>
        t === "Ticket"
          ? [
            { entity_id: "a", state: "new", severity_i: 2, created_at: 10 },
            { entity_id: "b", state: "triage", severity_i: 3, created_at: 5 },
            { entity_id: "c", state: "new", severity_i: 1, created_at: 1 },
          ]
          : [],
      sla_status: () => [],
      baseEnv: {
        now: 1,
        actor: "u",
        state: "",
        input: {},
        attrs: {},
        arg: {},
        intrinsics: {
          has_role: () => false,
          role_of: () => "agent",
          auth_ok: () => true,
          constraint: () => true,
          len: () => 0,
          str: (v) => (v === null ? null : String(v)),
          int: (v) => (typeof v === "number" ? Math.trunc(v) : null),
          float: (v) => (typeof v === "number" ? v : null),
        },
      } as any,
    }

    const q = {
      source: { snap: { type: "Ticket" } },
      pipeline: [
        { filter: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] } },
        {
          project: {
            fields: [
              { name: "id", expr: { var: { row: { field: "entity_id" } } } },
              { name: "sev", expr: { var: { row: { field: "severity_i" } } } },
              { name: "ts", expr: { var: { row: { field: "created_at" } } } },
            ],
          },
        },
        { order_by: [{ expr: { var: { row: { field: "sev" } } }, dir: "desc" }, { expr: { var: { row: { field: "ts" } } }, dir: "asc" }] },
      ],
    } as any

    const out = interpretQuery(q, ctx as any)
    assert.deepEqual(out.rows.map((r) => r.id), ["a", "c"])
  })

  it("adapter comparison hook (placeholder)", () => {
    // Once the SQLite adapter lowering emits SQL for a BoolQuery or View, compare:
    // 1) oracle interpretQuery(...) result rows
    // 2) adapter exec_view_sql({sql,binds}) rows
    //
    // Use randomized datasets to catch edge-case divergences.
    assert.ok(true)
  })
})
