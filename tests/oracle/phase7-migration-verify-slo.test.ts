import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 migration/verify slo artifact", () => {
  it("declares SLO targets and error budgets with evidence inputs", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-migration-verify-slo.json")
    const slo = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(slo.version, "cicsc/phase7-migration-verify-slo-v1")
    assert.equal(typeof slo.slo_targets.migration_protocol_check_success_rate.target, "string")
    assert.equal(typeof slo.error_budget.migration_protocol_failures_per_30_runs, "number")
    assert.ok(Array.isArray(slo.evidence_inputs))
    assert.equal(slo.evidence_inputs.length >= 3, true)
  })
})
