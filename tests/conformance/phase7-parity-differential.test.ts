import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 parity differential suites", () => {
  it("records green sqlite/postgres/oracle differential checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-parity-differential.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase7-parity-differential-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.sqlite_scope_matrix.status, "pass")
    assert.equal(report.checks.postgres_scope_matrix.status, "pass")
    assert.equal(report.checks.cross_backend_diff.status, "pass")
  })
})
