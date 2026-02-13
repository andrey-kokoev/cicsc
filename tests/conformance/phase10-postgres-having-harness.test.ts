import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase10 postgres having harness", () => {
  it("publishes continuity status with explicit deferred rationale", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase10-postgres-having-harness.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(report.version, "cicsc/phase10-postgres-having-harness-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.postgres_exec_vs_oracle_baseline.status, "pass")
    assert.equal(report.checks.phase9_having_report.status, "pass")
    assert.equal(report.notes.pg_having_harness_status, "deferred")
  })
})
