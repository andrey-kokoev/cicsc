import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 edgecase parity report", () => {
  it("records green deterministic edgecase parity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-edgecase-parity.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-edgecase-parity-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.baseline_edgecases.status, "pass")
    assert.equal(report.checks.having_edgecases.status, "pass")
  })
})
