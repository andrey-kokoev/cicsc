import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase17 closure report", () => {
  it("marks closure pass and unblocks phase18 gate", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase17-closure-report.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase17-closure-report-v1")
    assert.equal(r.status, "pass")
    assert.equal(r.phase18_gate_blocked, false)
  })
})
