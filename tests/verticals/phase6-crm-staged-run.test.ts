import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 crm staged run artifact", () => {
  it("records crm staged run checks with passing status", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-crm-staged-run.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase6-crm-staged-run-v1")
    assert.equal(report.vertical, "crm")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.crm_spec_usability.status, "pass")
    assert.equal(report.checks.conformance_postgres.status, "pass")
    assert.ok(Number(report.metrics.total_duration_ms) > 0)
  })
})
