import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { genSqliteSchemaFromIr } from "../../adapters/sqlite/src/schema/gen"
import type { CoreIrV0 } from "../../core/ir/types"

describe("sqlite schema generation", () => {
  it("generates snapshots_vN from IR shadows", () => {
    const ir: CoreIrV0 = {
      version: 0,
      types: {
        Ticket: {
          id_type: "string",
          states: ["new"],
          initial_state: "new",
          attrs: {},
          shadows: {
            severity_i: { type: "int" },
            created_at: { type: "time" },
          },
          commands: {
            c: { input: {}, guard: { expr: { lit: { bool: true } } as any }, emits: [] },
          },
          reducer: {},
        },
        Lead: {
          id_type: "string",
          states: ["new"],
          initial_state: "new",
          attrs: {},
          shadows: {
            score_f: { type: "float" },
          },
          commands: {
            c: { input: {}, guard: { expr: { lit: { bool: true } } as any }, emits: [] },
          },
          reducer: {},
        },
      },
    }

    const out = genSqliteSchemaFromIr(ir, { version: 7 }).sql

    assert.match(out, /CREATE TABLE IF NOT EXISTS snapshots_v7/i)
    assert.match(out, /"created_at" INTEGER/i)
    assert.match(out, /"severity_i" INTEGER/i)
    assert.match(out, /"score_f" REAL/i)
  })
})
