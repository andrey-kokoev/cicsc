import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase15 baseline continuity", () => {
  it("records pass baseline from phase14 closure and continuity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase15-baseline-continuity.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase15-baseline-continuity-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase14_exit_checklist.status, "pass")
    assert.equal(r.checks.phase15_gate_open.status, "pass")
    assert.equal(r.checks.generalization_continuity.status, "pass")
    assert.equal(r.checks.readiness_continuity.status, "pass")
  })
})
