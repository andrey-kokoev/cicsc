import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase10 parity continuity gate", () => {
  it("records green parity continuity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase10-parity-continuity.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(report.version, "cicsc/phase10-parity-continuity-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.phase9_required_gates.status, "pass")
    assert.equal(report.checks.phase10_postgres_having_harness.status, "pass")
  })
})
