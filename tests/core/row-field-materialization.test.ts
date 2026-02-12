import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { validateBundleV0 } from "../../core/ir/validate"

describe("row field materialization checks", () => {
  it("rejects bundle when view references non-materialized row field", () => {
    const bundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {
              priority: { type: "string" },
            },
            commands: {
              c: {
                input: {},
                guard: { expr: { lit: { bool: true } } },
                emits: [],
              },
            },
            reducer: {},
          },
        },
        views: {
          bad_view: {
            kind: "metric",
            on_type: "Ticket",
            query: {
              source: { snap: { type: "Ticket" } },
              pipeline: [
                {
                  project: {
                    fields: [
                      { name: "p", expr: { var: { row: { field: "priority" } } } },
                    ],
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
    assert.ok(v.errors.some((e) => e.message.includes("not core/shadow")))
  })
})
