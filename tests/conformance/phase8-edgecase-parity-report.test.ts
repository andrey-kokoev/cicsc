import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 edgecase parity report", () => {
  it("records green edgecase parity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-edgecase-parity.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase8-edgecase-parity-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.edgecase_dataset_contract.status, "pass")
    assert.equal(report.checks.backend_semantics_policy.status, "pass")
    assert.equal(report.checks.cross_backend_differential.status, "pass")
  })
})
