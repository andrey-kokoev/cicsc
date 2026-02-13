import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase10 closure report", () => {
  it("publishes pass closure with complete exit criteria and open phase11 gate", () => {
    const reportPath = path.resolve(process.cwd(), "docs/pilot/phase10-closure-report.json")
    const report = JSON.parse(fs.readFileSync(reportPath, "utf8"))

    const gatePath = path.resolve(process.cwd(), "docs/pilot/phase11-gate.json")
    const gate = JSON.parse(fs.readFileSync(gatePath, "utf8"))

    assert.equal(report.version, "cicsc/phase10-closure-report-v1")
    assert.equal(report.status, "pass")
    for (const item of report.exit_criteria ?? []) {
      assert.equal(item.status, "pass")
    }

    assert.equal(gate.version, "cicsc/phase11-gate-v1")
    assert.equal(gate.blocked, false)
    assert.deepEqual(gate.reasons, [])
  })
})
