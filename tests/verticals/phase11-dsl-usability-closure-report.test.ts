import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase11 dsl usability closure report", () => {
  it("publishes pass closure with explicit residual policy", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase11-dsl-usability-closure-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase11-dsl-usability-closure-report-v1")
    assert.equal(report.status, "pass")
    assert.equal(report.rubric_result.passes, true)
    assert.ok(report.rubric_result.task_success_rate >= report.rubric_result.cohort_threshold)
    assert.ok(Array.isArray(report.residuals))
    assert.deepEqual(report.residuals, [])
  })
})
