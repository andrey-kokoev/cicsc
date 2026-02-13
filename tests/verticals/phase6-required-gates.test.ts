import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 required gates", () => {
  it("requires green dual-backend + concurrency suites", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-required-gates.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase6-required-gates-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.dual_backend_conformance.status, "pass")
    assert.equal(report.checks.concurrency_suite.status, "pass")
  })
})
