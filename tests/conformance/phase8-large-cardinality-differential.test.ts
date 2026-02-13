import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 large-cardinality differential report", () => {
  it("records green large-snapshot/high-cardinality differential checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-large-cardinality-differential.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase8-large-cardinality-differential-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.sqlite_large_snapshots.status, "pass")
    assert.equal(report.checks.postgres_exec_vs_oracle.status, "pass")
    assert.equal(report.checks.cross_backend_diff.status, "pass")
  })
})
