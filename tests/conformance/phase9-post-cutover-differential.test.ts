import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 post-cutover differential", () => {
  it("records green migrated-stream and construct differential checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-post-cutover-differential.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase9-post-cutover-differential-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.migrated_streams.status, "pass")
    assert.equal(report.checks.having_construct.status, "pass")
  })
})
