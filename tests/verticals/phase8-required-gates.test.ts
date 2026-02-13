import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 required gates", () => {
  it("requires green equivalence + resilience + ergonomics safety suites", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-required-gates.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase8-required-gates-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.equivalence.status, "pass")
    assert.equal(report.checks.resilience.status, "pass")
    assert.equal(report.checks.ergonomics_safety.status, "pass")
  })
})
