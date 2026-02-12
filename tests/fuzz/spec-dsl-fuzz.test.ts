import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { parseSpecV0 } from "../../spec/parse-yaml"
import { typecheckSpecV0 } from "../../spec/typecheck"
import { compileSpecV0ToCoreIr } from "../../spec/compile-to-ir"

describe("spec DSL fuzzing (grammar-bounded)", () => {
  it("parses/typechecks/compiles random bounded specs without crashing", () => {
    const rng = makeRng(0xC1C5C)
    const ITER = 150

    for (let i = 0; i < ITER; i++) {
      const spec = genSpec(rng, i)

      const parsed = parseSpecV0(spec)
      const stc = typecheckSpecV0(parsed)
      if (!stc.ok) continue

      assert.doesNotThrow(() => {
        compileSpecV0ToCoreIr(parsed)
      })
    }
  })
})

function genSpec (rng: () => number, i: number): any {
  const states = ["new", "active", "done"].slice(0, 2 + Math.floor(rng() * 2))
  const event = `ev_${i}`

  return {
    version: 0,
    entities: {
      Ticket: {
        id: "string",
        states,
        initial: states[0],
        attributes: maybe(rng, {
          title: { type: "string" },
        }),
        commands: {
          run: {
            when: maybe(rng, { state_is: states[Math.floor(rng() * states.length)] }),
            emit: [{ type: event, payload: {} }],
          },
        },
        reducers: {
          [event]: maybe(rng, [{ set_state: states[states.length - 1] }], []),
        },
      },
    },
    views: maybe(rng, {
      board: {
        kind: "lanes",
        on: "Ticket",
        lanes: {
          states,
          order_by: { field: "updated_ts", dir: "desc" },
          limit: 10,
        },
      },
    }),
  }
}

function maybe<T> (rng: () => number, a: T, b: any = undefined): T | undefined {
  return rng() < 0.5 ? a : b
}

function makeRng (seed: number): () => number {
  let s = seed >>> 0
  return () => {
    s = (1664525 * s + 1013904223) >>> 0
    return s / 0x100000000
  }
}
