import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 post-cutover differential", () => {
  it("records green migration + sqlite/postgres differential checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-post-cutover-differential.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase7-post-cutover-differential-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.migration_replay_conformance.status, "pass")
    assert.equal(report.checks.sqlite_exec_vs_oracle_smoke.status, "pass")
    assert.equal(report.checks.postgres_exec_vs_oracle.status, "pass")
  })
})
