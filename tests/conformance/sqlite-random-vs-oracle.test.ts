// /tests/conformance/sqlite-random-vs-oracle.test.ts

import { describe, it } from "node:test"

import { generateCases } from "./random-query-generator"
import { assertSqliteOracleParity } from "./random-oracle-harness"

describe("conformance: sqlite random generated vs oracle", () => {
  it("matches oracle on generated query/snapshot cases", () => {
    const cases = generateCases(25, 2000)
    for (const c of cases) {
      try {
        assertSqliteOracleParity(c.query, c.snapRows)
      } catch (err: any) {
        throw new Error(`seed ${c.seed}: ${String(err?.message ?? err)}`)
      }
    }
  })
})
