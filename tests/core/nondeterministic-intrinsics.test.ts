import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { validateBundleV0 } from "../../core/ir/validate"

describe("non-deterministic intrinsic checks", () => {
  it("rejects non-deterministic intrinsic in command guard", () => {
    const bundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {},
            commands: {
              create: {
                input: {},
                guard: {
                  expr: {
                    call: { fn: "uuid", args: [] },
                  },
                },
                emits: [],
              },
            },
            reducer: {},
          },
        },
      },
    }

    const v = validateBundleV0(bundle)
    assert.equal(v.ok, false)
    if (v.ok) return
    assert.ok(v.errors.some((e) => e.message.includes("non-deterministic intrinsic")))
  })

  it("rejects non-deterministic intrinsic in reducer expression", () => {
    const bundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {
              score: { type: "int" },
            },
            commands: {
              c: { input: {}, guard: { expr: { lit: { bool: true } } }, emits: [] },
            },
            reducer: {
              e: [
                {
                  set_attr: {
                    name: "score",
                    expr: { call: { fn: "random", args: [] } },
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
    assert.ok(v.errors.some((e) => e.message.includes("non-deterministic intrinsic")))
  })
})
