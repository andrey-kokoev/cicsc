import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 sql surface closure report", () => {
  it("publishes construct status with residual exclusion ownership", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-sql-surface-closure-report.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-sql-surface-closure-report-v1")
    assert.equal(report.overall, "pass")

    const statuses = report.construct_status ?? []
    assert.ok(statuses.some((s: any) => s.construct === "having" && s.status === "enabled"))
    assert.ok(statuses.some((s: any) => s.construct === "exists" && s.status === "deferred"))

    for (const r of report.residual_exclusions ?? []) {
      assert.equal(typeof r.id, "string")
      assert.equal(typeof r.owner, "string")
      assert.match(r.target_date, /^\d{4}-\d{2}-\d{2}$/)
    }
  })
})
