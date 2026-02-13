import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 required gates", () => {
  it("requires green parity + concurrency + migration protocol suites", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-required-gates.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase7-required-gates-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.parity.status, "pass")
    assert.equal(report.checks.concurrency.status, "pass")
    assert.equal(report.checks.migration_protocol.status, "pass")
  })
})
