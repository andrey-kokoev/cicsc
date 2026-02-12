import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { validateBundleV0 } from "../../core/ir/validate"

describe("shadow type consistency", () => {
  it("rejects bundle when same shadow has conflicting types across entity types", () => {
    const bundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {},
            shadows: {
              priority_i: { type: "int" },
            },
            commands: {
              c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] },
            },
            reducer: {},
          },
          Incident: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {},
            shadows: {
              priority_i: { type: "string" },
            },
            commands: {
              c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] },
            },
            reducer: {},
          },
        },
      },
    }

    const v = validateBundleV0(bundle)
    assert.equal(v.ok, false)
    if (v.ok) return
    assert.ok(v.errors.some((e) => e.message.includes("inconsistent types")))
  })

  it("rejects bundle when shared shadow type is implicit in one type and explicit in another", () => {
    const bundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {},
            shadows: {
              created_at: { type: "time" },
            },
            commands: {
              c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] },
            },
            reducer: {},
          },
          Incident: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {},
            shadows: {
              created_at: {},
            },
            commands: {
              c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] },
            },
            reducer: {},
          },
        },
      },
    }

    const v = validateBundleV0(bundle)
    assert.equal(v.ok, false)
    if (v.ok) return
    assert.ok(v.errors.some((e) => e.message.includes("must be explicitly")))
  })
})
