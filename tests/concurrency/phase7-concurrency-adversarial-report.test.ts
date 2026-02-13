import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 concurrency adversarial report", () => {
  it("records green adversarial multi-tenant and cross-stream suites", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-concurrency-adversarial.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase7-concurrency-adversarial-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.phase7_multitenant_replay.status, "pass")
    assert.equal(report.checks.causality_replay.status, "pass")
    assert.equal(report.checks.replay_multistream.status, "pass")
    assert.equal(report.checks.transaction_model.status, "pass")
  })
})
