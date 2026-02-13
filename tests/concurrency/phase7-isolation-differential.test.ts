import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 isolation differential report", () => {
  it("records green backend differential checks for declared invariants", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-isolation-differential.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase7-isolation-differential-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.cross_backend_diff.status, "pass")
    assert.equal(report.checks.runtime_seq_isolation.status, "pass")
    assert.equal(report.checks.transaction_model.status, "pass")
  })
})
