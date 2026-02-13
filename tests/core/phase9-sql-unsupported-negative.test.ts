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

describe("phase9 unsupported SQL negative coverage", () => {
  it("rejects HAVING when no preceding group_by exists", () => {
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
    assert.ok(v.errors.some((e) => e.message.includes("requires a preceding group_by")))
  })

  it("rejects unknown query operators with explicit diagnostics", () => {
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
              pipeline: [{ set_op: { union: true } }],
            },
          },
        },
      },
    }

    const v = validateBundleV0(bundle)
    assert.equal(v.ok, false)
    if (v.ok) return
    assert.ok(v.errors.some((e) => e.message.includes("unknown op 'set_op'")))
  })
})
