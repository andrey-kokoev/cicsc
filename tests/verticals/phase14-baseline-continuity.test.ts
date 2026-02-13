import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase14 baseline continuity", () => {
  it("records pass baseline from phase13 closure and continuity checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase14-baseline-continuity.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase14-baseline-continuity-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.phase13_exit_checklist.status, "pass")
    assert.equal(r.checks.phase14_gate_open.status, "pass")
    assert.equal(r.checks.scale_continuity.status, "pass")
    assert.equal(r.checks.hardening_continuity.status, "pass")
  })
})
