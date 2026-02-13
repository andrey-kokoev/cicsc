import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase19 runtime reliability closure report", () => {
  it("publishes residual policy with no unresolved criticals", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase19-runtime-reliability-closure-report.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(r.version, "cicsc/phase19-runtime-reliability-closure-report-v1")
    assert.equal(r.status, "pass")
    assert.deepEqual(r.unresolved_criticals, [])
  })
})
