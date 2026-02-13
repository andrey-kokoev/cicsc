import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase19 baseline continuity", () => {
  it("records pass baseline from phase18 closure and continuity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase19-baseline-continuity.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(r.version, "cicsc/phase19-baseline-continuity-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase18_exit_checklist.status, "pass")
    assert.equal(r.checks.phase19_gate_open.status, "pass")
    assert.equal(r.checks.expansion_proof_continuity.status, "pass")
    assert.equal(r.checks.production_continuity_continuity.status, "pass")
  })
})
