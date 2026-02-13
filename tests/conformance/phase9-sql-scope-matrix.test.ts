import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 sql scope matrix", () => {
  it("freezes supported/candidate/deferred SQL envelope", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-sql-scope-matrix.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-sql-scope-matrix-v1")
    assert.ok(Array.isArray(report.supported_now))
    assert.ok(report.supported_now.includes("where"))

    const candidates = report.expansion_candidates ?? []
    assert.ok(candidates.some((c: any) => c.construct === "having"))
    assert.ok(candidates.some((c: any) => c.construct === "exists"))
    for (const c of candidates) {
      assert.equal(c.status, "candidate")
      assert.equal(c.gate, "oracle_differential_required")
    }

    const deferred = report.deferred ?? []
    for (const d of deferred) {
      assert.equal(d.status, "deferred")
      assert.equal(typeof d.owner, "string")
      assert.match(d.target_date, /^\d{4}-\d{2}-\d{2}$/)
    }
  })
})
