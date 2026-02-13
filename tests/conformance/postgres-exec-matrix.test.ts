import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

function readJson (fileName: string): any {
  const p = path.resolve(process.cwd(), "tests/conformance", fileName)
  return JSON.parse(fs.readFileSync(p, "utf8"))
}

describe("postgres execution matrix contract", () => {
  it("tracks supported query operators from postgres scope contract", () => {
    const matrix = readJson("postgres-exec-matrix.json")
    const scope = readJson("postgres-supported-scope.json")

    assert.equal(matrix.version, "cicsc/postgres-exec-matrix-v1")
    assert.equal(scope.version, "cicsc/backend-scope-v1")
    assert.equal(scope.backend, "postgres")

    const covered = new Set<string>()
    for (const c of matrix.cases ?? []) {
      for (const op of c.operators ?? []) covered.add(String(op))
    }

    const missing = (scope.query?.supported ?? []).filter((op: string) => !covered.has(op))
    assert.deepEqual(missing, [])
  })
})
