import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

function readJson(rel: string): any {
  const p = path.resolve(process.cwd(), rel)
  return JSON.parse(fs.readFileSync(p, "utf8"))
}

describe("phase7 parity scope matrix", () => {
  it("freezes parity scope aligned with backend supported scopes", () => {
    const matrix = readJson("docs/pilot/phase7-parity-scope-matrix.json")
    const sqliteScope = readJson("tests/conformance/sqlite-supported-scope.json")
    const pgScope = readJson("tests/conformance/postgres-supported-scope.json")

    assert.equal(matrix.version, "cicsc/phase7-parity-scope-matrix-v1")
    assert.deepEqual(matrix.query_operators.in_scope, sqliteScope.query.supported)
    assert.deepEqual(matrix.query_operators.in_scope, pgScope.query.supported)
    assert.deepEqual(matrix.expression_operators.in_scope, sqliteScope.expr.supported)
    assert.deepEqual(matrix.expression_operators.in_scope, pgScope.expr.supported)
  })

  it("includes explicit null/collation/numeric parity axes", () => {
    const matrix = readJson("docs/pilot/phase7-parity-scope-matrix.json")
    assert.equal(typeof matrix.semantics_axes.null_ordering.policy, "string")
    assert.equal(typeof matrix.semantics_axes.collation.policy, "string")
    assert.equal(typeof matrix.semantics_axes.numeric.policy, "string")
  })
})
