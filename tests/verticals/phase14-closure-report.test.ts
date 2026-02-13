import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase14 closure report", () => {
  it("marks closure pass and unblocks phase15 gate", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase14-closure-report.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase14-closure-report-v1")
    assert.equal(r.status, "pass")
    assert.equal(r.phase15_gate_blocked, false)
  })
})
