// /tests/conformance/sqlite-lowering-vs-oracle.test.ts

import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { interpretQuery } from "../../core/query/interpret"
import { lowerQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"
import { lowerBoolQueryConstraintToSql } from "../../adapters/sqlite/src/lower/constraint-to-sql"

// This test compares *lowered SQL* against oracle semantics at the level of "shape + intent".
// It does not execute SQL (no D1 here). Execution comparison will be done once runtime/db harness exists.
describe("conformance: sqlite lowering vs oracle (shape)", () => {
  it("lowers a simple snap query and matches oracle expected ordering", () => {
    const q: any = {
      source: { snap: { type: "Ticket" } },
      pipeline: [
        { filter: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] } },
        { project: { fields: [{ name: "id", expr: { var: { row: { field: "entity_id" } } } }, { name: "sev", expr: { var: { row: { field: "severity_i" } } } }] } },
        { order_by: [{ expr: { var: { row: { field: "sev" } } }, dir: "desc" }] },
        { limit: 10 },
      ],
    }

    const plan = lowerQueryToSql(q, { version: 0, tenant_id: "t" })
    assert.ok(plan.sql.includes("FROM"))
    assert.ok(plan.sql.includes("snapshots_v0"))
    assert.ok(plan.sql.includes("ORDER BY"))

    // oracle sanity
    const ctx: any = {
      now: 1,
      actor: "u",
      snap: () => [
        { entity_id: "a", state: "new", severity_i: 2 },
        { entity_id: "b", state: "triage", severity_i: 3 },
        { entity_id: "c", state: "new", severity_i: 1 },
      ],
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
          str: (v: any) => (v === null ? null : String(v)),
          int: (v: any) => (typeof v === "number" ? Math.trunc(v) : null),
          float: (v: any) => (typeof v === "number" ? v : null),
        },
      },
    }

    const out = interpretQuery(q, ctx)
    assert.deepEqual(out.rows.map((r: any) => r.id), ["a", "c"])
  })

  it("lowers bool_query constraint to ok query with args", () => {
    const constraint: any = {
      kind: "bool_query",
      on_type: "Ticket",
      args: { limit: { type: "int" } },
      query: {
        source: { snap: { type: "Ticket" } },
        pipeline: [
          { filter: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] } },
        ],
      },
      assert: { le: [{ var: { rows_count: true } }, { var: { arg: { name: "limit" } } }] },
    }

    const plan = lowerBoolQueryConstraintToSql({
      constraint,
      version: 0,
      tenant_id: "t",
      args: { limit: 2 },
    })

    assert.ok(plan.sql.includes("SELECT CASE WHEN"))
    assert.ok(plan.sql.includes("COUNT(1) AS rows_count"))
    assert.ok(plan.binds.length >= 3) // tenant + type + limit at least
  })
})
