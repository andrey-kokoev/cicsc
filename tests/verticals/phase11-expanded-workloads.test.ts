import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase11 expanded workloads", () => {
  it("records pass suite for workload plus parity/migration/ops gates", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase11-expanded-workloads.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase11-expanded-workloads-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.reference_workloads.status, "pass")
    assert.equal(report.checks.parity_continuity.status, "pass")
    assert.equal(report.checks.migration_continuity.status, "pass")
    assert.equal(report.checks.operational_slo_continuity.status, "pass")
  })
})
