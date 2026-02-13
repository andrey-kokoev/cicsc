import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase18 baseline continuity", () => {
  it("records pass baseline from phase17 closure and continuity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase18-baseline-continuity.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase18-baseline-continuity-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase17_exit_checklist.status, "pass")
    assert.equal(r.checks.phase18_gate_open.status, "pass")
    assert.equal(r.checks.field_program_continuity.status, "pass")
    assert.equal(r.checks.trust_hardening_continuity.status, "pass")
  })
})
