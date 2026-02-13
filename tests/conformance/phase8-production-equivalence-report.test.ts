import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 production-equivalence report", () => {
  it("publishes exclusions and risk labels explicitly", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-production-equivalence-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase8-production-equivalence-report-v1")
    assert.equal(report.overall, "pass")
    assert.ok(Array.isArray(report.exclusions))
    assert.ok(Array.isArray(report.risk_labels))
    assert.equal(report.exclusions.length >= 1, true)
    assert.equal(report.risk_labels.length >= 1, true)
  })
})
