import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase18 expansion-proof required gates", () => {
  it("records pass suite for required expansion-proof gates", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase18-expansion-proof-required-gates.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase18-expansion-proof-required-gates-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase17_doc_consistency_status.status, "pass")
    assert.equal(r.checks.phase17_field_program_required_gates_status.status, "pass")
    assert.equal(r.checks.phase18_baseline_continuity_status.status, "pass")
  })
})
