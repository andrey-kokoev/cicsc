import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 having differential report", () => {
  it("records green sqlite/postgres execution-vs-oracle checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-having-differential.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-having-differential-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.sqlite_having_exec_vs_oracle.status, "pass")
    assert.ok(["pass", "deferred"].includes(report.checks.postgres_having_exec_vs_oracle.status))
  })
})
