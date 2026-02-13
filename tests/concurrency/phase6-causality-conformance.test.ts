import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 causality/partial-order conformance report", () => {
  it("records green status for declared concurrency model checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-concurrency-conformance.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase6-concurrency-conformance-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.causality_replay.status, "pass")
    assert.equal(report.checks.transaction_model.status, "pass")
    assert.equal(report.checks.replay_multistream.status, "pass")
  })
})
