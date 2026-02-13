import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase5 conformance gate policy", () => {
  it("requires sqlite and postgres profiles in mandatory gate scripts/matrix", () => {
    const matrixPath = path.resolve(process.cwd(), "tests/conformance/required-matrix.json")
    const matrix = JSON.parse(fs.readFileSync(matrixPath, "utf8"))

    const requiredSuites = (matrix.suites ?? []).filter((s: any) => s.required === true)
    const hasSqlite = requiredSuites.some((s: any) => s.backend === "sqlite")
    const hasPostgres = requiredSuites.some((s: any) => s.backend === "postgres" || s.backend === "multi")
    assert.equal(hasSqlite, true)
    assert.equal(hasPostgres, true)

    const gatePath = path.resolve(process.cwd(), "scripts/check_phase5_conformance_gates.sh")
    assert.equal(fs.existsSync(gatePath), true)
  })
})
