import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase12 parity envelope closure report", () => {
  it("publishes pass closure with explicit residual policy", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase12-parity-envelope-closure-report.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase12-parity-envelope-closure-report-v1")
    assert.equal(r.status, "pass")
    assert.deepEqual(r.unresolved_criticals, [])
    for (const x of r.residuals ?? []) {
      if (x.status === "deferred") {
        assert.equal(typeof x.owner, "string")
        assert.match(x.target_date, /^\d{4}-\d{2}-\d{2}$/)
      }
    }
  })
})
