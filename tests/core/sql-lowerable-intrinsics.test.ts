import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { validateBundleV0 } from "../../core/ir/validate"

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

describe("SQL-lowerable intrinsic checks", () => {
  it("rejects non-SQL intrinsics in views", () => {
    const bundle = {
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
                    call: {
                      fn: "has_role",
                      args: [{ var: { actor: true } }, { lit: { string: "agent" } }],
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
    assert.ok(v.errors.some((e) => e.message.includes("not allowed in SQL-lowered context")))
  })

  it("rejects non-SQL intrinsics in bool_query constraints", () => {
    const bundle = {
      core_ir: {
        version: 0,
        types: { Ticket: baseType() },
        constraints: {
          c1: {
            kind: "bool_query",
            on_type: "Ticket",
            args: {},
            query: {
              source: { snap: { type: "Ticket" } },
              pipeline: [
                {
                  filter: {
                    call: {
                      fn: "auth_ok",
                      args: [{ var: { actor: true } }, { lit: { string: "Ticket.close" } }],
                    },
                  },
                },
              ],
            },
            assert: { lit: { bool: true } },
          },
        },
      },
    }

    const v = validateBundleV0(bundle)
    assert.equal(v.ok, false)
    if (v.ok) return
    assert.ok(v.errors.some((e) => e.message.includes("not allowed in SQL-lowered context")))
  })
})
