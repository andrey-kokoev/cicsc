import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 fairness checks report", () => {
  it("records green fairness/starvation checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-fairness-checks.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase8-fairness-checks-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.fairness_starvation.status, "pass")
    assert.equal(report.checks.execute_batch.status, "pass")
  })
})
