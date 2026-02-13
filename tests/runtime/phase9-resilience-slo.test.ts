import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 resilience slo gate", () => {
  it("records green verify/migrate/command error-budget checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-resilience-slo.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-resilience-slo-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.phase8_baseline_slo.status, "pass")
    assert.equal(report.checks.phase9_required_gates.status, "pass")
    assert.equal(report.checks.phase9_migration_drills.status, "pass")
  })
})
