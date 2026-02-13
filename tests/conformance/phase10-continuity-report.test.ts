import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase10 continuity report", () => {
  it("enforces unresolved critical policy with owner/date deferred discipline", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase10-continuity-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase10-continuity-report-v1")
    assert.equal(report.overall, "pass")
    assert.deepEqual(report.unresolved_criticals, [])

    for (const c of report.continuity_checks ?? []) {
      assert.equal(c.status, "pass")
    }

    for (const f of report.finding_disposition ?? []) {
      if (f.status === "deferred") {
        assert.equal(typeof f.owner, "string")
        assert.match(f.target_date, /^\d{4}-\d{2}-\d{2}$/)
      }
      if (f.severity === "critical") {
        assert.ok(["closed", "deferred"].includes(f.status))
      }
    }
  })
})
