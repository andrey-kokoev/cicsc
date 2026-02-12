import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { typecheckCoreIrV0 } from "../../core/ir/typecheck"

describe("IR typechecker fuzzing", () => {
  it("handles malformed IR cases without crashing", () => {
    const rng = makeRng(0x10BAD >>> 0)
    const ITER = 180

    for (let i = 0; i < ITER; i++) {
      const ir = genMalformedIr(rng, i)
      assert.doesNotThrow(() => {
        typecheckCoreIrV0(ir as any)
      })
      const tc = typecheckCoreIrV0(ir as any)
      assert.equal(tc.ok, false)
    }
  })
})

function genMalformedIr (rng: () => number, i: number): any {
  const badField = `bad_field_${i}`
  const badIntrinsic = `bad_intrinsic_${i}`
  const malformedReducer = rng() < 0.5

  return {
    version: 0,
    types: {
      Ticket: {
        id_type: "string",
        states: ["new", "done"],
        initial_state: "new",
        attrs: {},
        shadows: {},
        commands: {
          close: {
            input: {},
            guard: {
              expr: rng() < 0.5
                ? { call: { fn: badIntrinsic, args: [] } } // illegal intrinsic
                : {
                    eq: [
                      { var: { row: { field: badField } } }, // illegal row field
                      { lit: { string: "x" } },
                    ],
                  },
            },
            emits: [{ event_type: "closed", payload: {} }],
          },
        },
        reducer: malformedReducer
          ? { closed: [{ unknown_op: { x: 1 } }] } // malformed reducer op
          : { closed: [{ set_attr: { name: "missing_attr", expr: { lit: { string: "x" } } } }] }, // illegal write
      },
    },
  }
}

function makeRng (seed: number): () => number {
  let s = seed >>> 0
  return () => {
    s = (1664525 * s + 1013904223) >>> 0
    return s / 0x100000000
  }
}
