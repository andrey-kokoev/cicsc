import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase19 deployment-assurance closure report", () => {
  it("publishes findings disposition with no unresolved criticals", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase19-deployment-assurance-closure-report.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))
    assert.equal(r.version, "cicsc/phase19-deployment-assurance-closure-report-v1")
    assert.equal(r.status, "pass")
    assert.deepEqual(r.unresolved_criticals, [])
  })
})
