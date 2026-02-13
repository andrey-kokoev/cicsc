import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase17 baseline continuity", () => {
  it("records pass baseline from phase16 closure and continuity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase17-baseline-continuity.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase17-baseline-continuity-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase16_exit_checklist.status, "pass")
    assert.equal(r.checks.phase17_gate_open.status, "pass")
    assert.equal(r.checks.external_validation_continuity.status, "pass")
    assert.equal(r.checks.expansion_hardening_continuity.status, "pass")
  })
})
