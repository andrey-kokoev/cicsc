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

  it("generates indexes from view filter/order_by row fields", () => {
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
      },
      views: {
        lane_view: {
          kind: "metric",
          on_type: "Ticket",
          query: {
            source: { snap: { type: "Ticket" } },
            pipeline: [
              {
                filter: {
                  and: [
                    { eq: [{ var: { row: { field: "severity_i" } } }, { lit: { int: 2 } }] },
                    { eq: [{ var: { row: { field: "state" } } }, { lit: { string: "new" } }] },
                  ],
                },
              },
              {
                order_by: [
                  { expr: { var: { row: { field: "created_at" } } }, dir: "desc" },
                ],
              },
            ],
          },
        },
      },
    }

    const out = genSqliteSchemaFromIr(ir, { version: 3 }).sql

    assert.match(out, /CREATE INDEX IF NOT EXISTS idx_snapshots_v3_view_created_at/i)
    assert.match(out, /CREATE INDEX IF NOT EXISTS idx_snapshots_v3_view_severity_i/i)
    assert.doesNotMatch(out, /idx_snapshots_v3_view_state/i)
  })

  it("generates indexes from bool_query constraint filter fields", () => {
    const ir: CoreIrV0 = {
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
            c: { input: {}, guard: { expr: { lit: { bool: true } } as any }, emits: [] },
          },
          reducer: {},
        },
      },
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
                  lt: [{ var: { row: { field: "created_at" } } }, { lit: { int: 100 } }],
                },
              },
            ],
          },
          assert: { lit: { bool: true } },
        },
      },
    }

    const out = genSqliteSchemaFromIr(ir, { version: 4 }).sql
    assert.match(out, /CREATE INDEX IF NOT EXISTS idx_snapshots_v4_constraint_created_at/i)
  })
})
