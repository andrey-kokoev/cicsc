import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase16 external-validation closure report", () => {
  it("publishes findings disposition with no unresolved criticals", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase16-external-validation-closure-report.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase16-external-validation-closure-report-v1")
    assert.equal(r.status, "pass")
    assert.deepEqual(r.unresolved_criticals, [])
    for (const f of r.findings ?? []) {
      if (f.status === "deferred") {
        assert.equal(typeof f.owner, "string")
        assert.match(f.target_date, /^\d{4}-\d{2}-\d{2}$/)
      }
    }
  })
})
