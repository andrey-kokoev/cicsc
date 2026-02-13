import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 backend parity report", () => {
  it("publishes in-scope pass statuses with explicit exclusions", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-backend-parity-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase7-backend-parity-report-v1")
    assert.equal(report.overall, "pass")

    for (const status of Object.values(report.in_scope_operator_status.query)) {
      assert.equal(status, "pass")
    }
    for (const status of Object.values(report.in_scope_operator_status.expr)) {
      assert.equal(status, "pass")
    }

    assert.deepEqual(report.exclusions.query, ["op:having", "op:distinct", "op:setOp"])
    assert.deepEqual(report.exclusions.expr, ["expr:exists"])
  })
})
