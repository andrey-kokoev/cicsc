import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 fail-fast out-of-scope gate", () => {
  it("records green fail-fast checks for deferred/unsupported constructs", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-failfast-scope.json")
    const report = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(report.version, "cicsc/phase7-failfast-scope-v1")
    assert.equal(report.overall, "pass")
    assert.equal(report.checks.scope_contracts.status, "pass")
    assert.equal(report.checks.failfast_rejections.status, "pass")
    assert.equal(report.checks.unsupported_feature_policy.status, "pass")
  })
})
