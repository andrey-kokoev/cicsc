import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 reference workloads", () => {
  it("records green reference workload gate runs", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-reference-workloads.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-reference-workloads-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.ticketing_spec_usability.status, "pass")
    assert.equal(report.checks.crm_spec_usability.status, "pass")
    assert.equal(report.checks.phase9_required_gates.status, "pass")
    assert.equal(report.checks.phase9_migration_drills.status, "pass")
  })
})
