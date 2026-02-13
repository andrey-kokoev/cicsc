import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

function readJson (fileName: string): any {
  const p = path.resolve(process.cwd(), "tests/conformance", fileName)
  return JSON.parse(fs.readFileSync(p, "utf8"))
}

describe("postgres constraint matrix contract", () => {
  it("declares lowered constraint kinds and deferred reducer conformance explicitly", () => {
    const matrix = readJson("postgres-constraint-matrix.json")

    assert.equal(matrix.version, "cicsc/postgres-constraint-matrix-v1")
    assert.deepEqual(matrix.constraint_kinds, ["bool_query"])
    assert.equal(matrix.reducer_lowering?.status, "not_implemented")
    assert.equal(matrix.reducer_lowering?.conformance, "deferred_until_lowering_exists")
    assert.ok(Array.isArray(matrix.cases))
    assert.ok(matrix.cases.length >= 2)
  })
})
