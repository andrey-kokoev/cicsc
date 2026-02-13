import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { validateBundleV0 } from "../../core/ir/validate"
import { lowerQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"

function baseType () {
  return {
    id_type: "string",
    states: ["new"],
    initial_state: "new",
    attrs: {},
    commands: {
      c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] },
    },
    reducer: {},
  }
}

describe("phase9 sql feature gates", () => {
  it("rejects HAVING op via explicit feature gate diagnostic", () => {
    const bundle: any = {
      core_ir: {
        version: 0,
        types: { Ticket: baseType() },
        views: {
          bad: {
            kind: "metric",
            on_type: "Ticket",
            query: {
              source: { snap: { type: "Ticket" } },
              pipeline: [{ having: { lit: { bool: true } } }],
            },
          },
        },
      },
    }

    const v = validateBundleV0(bundle)
    assert.equal(v.ok, false)
    if (v.ok) return
    assert.ok(v.errors.some((e) => e.message.includes("phase9.sql.having")))
  })

  it("rejects EXISTS expr via explicit feature gate diagnostic", () => {
    const bundle: any = {
      core_ir: {
        version: 0,
        types: { Ticket: baseType() },
        views: {
          bad: {
            kind: "metric",
            on_type: "Ticket",
            query: {
              source: { snap: { type: "Ticket" } },
              pipeline: [
                {
                  filter: {
                    exists: {
                      query: { source: { snap: { type: "Ticket" } }, pipeline: [] },
                    },
                  },
                },
              ],
            },
          },
        },
      },
    }

    const v = validateBundleV0(bundle)
    assert.equal(v.ok, false)
    if (v.ok) return
    assert.ok(v.errors.some((e) => e.message.includes("phase9.sql.exists")))
  })

  it("sqlite lowerer rejects gated HAVING/EXISTS even if bypassing validator", () => {
    assert.throws(
      () => lowerQueryToSql({ source: { snap: { type: "Ticket" } }, pipeline: [{ having: { lit: { bool: true } } }] } as any, { version: 0, tenant_id: "t" }),
      /phase9\.sql\.having/
    )

    assert.throws(
      () => lowerQueryToSql({ source: { snap: { type: "Ticket" } }, pipeline: [{ filter: { exists: { query: { source: { snap: { type: "Ticket" } }, pipeline: [] } } } }] } as any, { version: 0, tenant_id: "t" }),
      /phase9\.sql\.exists/
    )
  })
})
