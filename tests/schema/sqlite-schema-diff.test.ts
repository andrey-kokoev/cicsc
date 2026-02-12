import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { genSnapshotsSchemaDiff } from "../../adapters/sqlite/src/schema/diff"
import type { CoreIrV0 } from "../../core/ir/types"

function mk (shadows: Record<string, any>): CoreIrV0 {
  return {
    version: 0,
    types: {
      Ticket: {
        id_type: "string",
        states: ["new"],
        initial_state: "new",
        attrs: {},
        shadows,
        commands: {
          c: { input: {}, guard: { expr: { lit: { bool: true } } as any }, emits: [] },
        },
        reducer: {},
      },
    },
  }
}

describe("sqlite snapshot schema diff", () => {
  it("emits ADD COLUMN for new shadows", () => {
    const previous = mk({ severity_i: { type: "int" } })
    const next = mk({ severity_i: { type: "int" }, created_at: { type: "time" } })

    const out = genSnapshotsSchemaDiff({ previous, next, version: 2 })
    assert.deepEqual(out.statements, [
      'ALTER TABLE snapshots_v2 ADD COLUMN "created_at" INTEGER;',
    ])
  })

  it("fails on incompatible shadow type change", () => {
    const previous = mk({ severity_i: { type: "int" } })
    const next = mk({ severity_i: { type: "string" } })

    assert.throws(
      () => genSnapshotsSchemaDiff({ previous, next, version: 2 }),
      /incompatible shadow type change/
    )
  })
})
