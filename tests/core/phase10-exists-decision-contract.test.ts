import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase10 exists decision contract", () => {
  it("declares explicit deferred policy and enablement prerequisites", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase10-exists-decision-contract.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(report.version, "cicsc/phase10-exists-decision-contract-v1")
    assert.equal(report.decision.status, "deferred")
    assert.equal(report.decision.policy, "compile_time_reject")
    assert.equal(typeof report.decision.owner, "string")
    assert.match(report.decision.target_date, /^\d{4}-\d{2}-\d{2}$/)
    assert.ok((report.enablement_prerequisites ?? []).length >= 4)
  })
})
