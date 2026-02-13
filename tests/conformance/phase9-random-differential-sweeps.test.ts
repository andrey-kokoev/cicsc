import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 random differential sweeps report", () => {
  it("records green seeded random differential checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-random-differential-sweeps.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-random-differential-sweeps-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.sqlite_seeded_random.status, "pass")
    assert.equal(report.checks.cross_backend_differential.status, "pass")
  })
})
