import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase16 expansion hardening closure report", () => {
  it("publishes residual policy with no unresolved criticals", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase16-expansion-hardening-closure-report.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase16-expansion-hardening-closure-report-v1")
    assert.equal(r.status, "pass")
    assert.deepEqual(r.unresolved_criticals, [])
    for (const residual of r.residuals ?? []) {
      if (residual.status === "deferred") {
        assert.equal(typeof residual.owner, "string")
        assert.match(residual.target_date, /^\d{4}-\d{2}-\d{2}$/)
      }
    }
  })
})
