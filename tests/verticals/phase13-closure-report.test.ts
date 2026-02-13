import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase13 closure report", () => {
  it("publishes pass closure with full exit criteria and open phase14 gate", () => {
    const rp = path.resolve(process.cwd(), "docs/pilot/phase13-closure-report.json")
    const gp = path.resolve(process.cwd(), "docs/pilot/phase14-gate.json")
    const report = JSON.parse(fs.readFileSync(rp, "utf8"))
    const gate = JSON.parse(fs.readFileSync(gp, "utf8"))

    assert.equal(report.version, "cicsc/phase13-closure-report-v1")
    assert.equal(report.status, "pass")
    for (const i of report.exit_criteria ?? []) assert.equal(i.status, "pass")

    assert.equal(gate.version, "cicsc/phase14-gate-v1")
    assert.equal(gate.blocked, false)
    assert.deepEqual(gate.reasons, [])
  })
})
