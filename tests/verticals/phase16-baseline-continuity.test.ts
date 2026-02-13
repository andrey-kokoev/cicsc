import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase16 baseline continuity", () => {
  it("records pass baseline from phase15 closure and continuity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase16-baseline-continuity.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase16-baseline-continuity-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase15_exit_checklist.status, "pass")
    assert.equal(r.checks.phase16_gate_open.status, "pass")
    assert.equal(r.checks.objective_continuity.status, "pass")
    assert.equal(r.checks.deferred_surface_continuity.status, "pass")
  })
})
