import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { lowerBoolQueryConstraintToSql } from "../../adapters/postgres/src/lower/constraint-to-sql"

describe("postgres constraint lowering shape", () => {
  it("lowers bool_query to postgres parameterized SQL shape", () => {
    const constraint: any = {
      kind: "bool_query",
      on_type: "Ticket",
      args: { limit: { type: "int" } },
      query: {
        source: { snap: { type: "Ticket" } },
        pipeline: [{ filter: { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] } }],
      },
      assert: { le: [{ var: { rows_count: true } }, { var: { arg: { name: "limit" } } }] },
    }

    const plan = lowerBoolQueryConstraintToSql({
      constraint,
      version: 0,
      tenant_id: "t",
      args: { limit: 2 },
    })

    assert.match(plan.sql, /\$1/)
    assert.match(plan.sql, /\$2/)
    assert.equal(Array.isArray(plan.binds), true)
    assert.equal(plan.binds.length >= 2, true)
  })
})
