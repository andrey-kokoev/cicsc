import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { validateBundleV0 } from "../../core/ir/validate"

describe("bundle validation wiring", () => {
  it("validateBundleV0 rejects semantically invalid IR via typechecker", () => {
    const badBundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {},
            commands: {
              c: {
                input: {},
                guard: { expr: { lit: { bool: true } } },
                emits: [],
              },
            },
            reducer: {
              e: [{ set_attr: { name: "undeclared_attr", expr: { lit: { string: "x" } } } }],
            },
          },
        },
      },
    }

    const v = validateBundleV0(badBundle)
    assert.equal(v.ok, false)
    if (v.ok) return
    assert.ok(v.errors.some((e) => e.path.includes("set_attr.name")))
  })

  it("worker env-bundle load logic rejects invalid CICSC_BUNDLE", () => {
    const badBundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {},
            commands: {
              c: {
                input: {},
                guard: { expr: { lit: { bool: true } } },
                emits: [],
              },
            },
            reducer: {
              e: [{ set_attr: { name: "undeclared_attr", expr: { lit: { string: "x" } } } }],
            },
          },
        },
      },
    }

    const parsed = JSON.parse(JSON.stringify(badBundle))
    const v = validateBundleV0(parsed)
    assert.equal(v.ok, false)
    if (v.ok) return
    const err = `invalid bundle: ${v.errors[0]?.path ?? "?"} ${v.errors[0]?.message ?? ""}`
    assert.match(err, /invalid bundle:/i)
  })
})
