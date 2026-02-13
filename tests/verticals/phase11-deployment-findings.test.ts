import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase11 deployment findings", () => {
  it("captures severity-labeled findings with deferred owner/date discipline", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase11-deployment-findings.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase11-deployment-findings-v1")
    assert.equal(report.status, "pass")
    assert.deepEqual(report.unresolved_criticals, [])
    assert.ok(Array.isArray(report.findings))
    for (const f of report.findings) {
      assert.ok(["low", "medium", "high", "critical"].includes(f.severity))
      if (f.status === "deferred") {
        assert.equal(typeof f.owner, "string")
        assert.match(f.target_date, /^\d{4}-\d{2}-\d{2}$/)
      }
    }
  })
})
