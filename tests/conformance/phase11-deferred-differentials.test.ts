import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase11 deferred differentials", () => {
  it("records pass differential/negative coverage for deferred constructs", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase11-deferred-differentials.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase11-deferred-differentials-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.having_exec_vs_oracle.status, "pass")
    assert.equal(report.checks.having_postgres_harness.status, "pass")
    assert.equal(report.checks.exists_feature_gate_negative.status, "pass")
  })
})
