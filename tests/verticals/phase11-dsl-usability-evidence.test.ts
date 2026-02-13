import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase11 dsl usability evidence", () => {
  it("captures reproducible usability outcomes and metrics", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase11-dsl-usability-evidence.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase11-dsl-usability-evidence-v1")
    assert.equal(report.overall, "pass")
    assert.ok(report.metrics.task_success_rate >= 0.8)
    assert.equal(report.checks.ticketing_create_guard.status, "pass")
    assert.equal(report.checks.crm_pipeline_evolution.status, "pass")
    assert.equal(report.checks.migration_authoring_usability.status, "pass")
  })
})
