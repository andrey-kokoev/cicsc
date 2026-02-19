import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { isDeployable, normalizeBlockingIssues } from "../../core/assistant/blocking-policy.ts"

describe("blocking policy", () => {
  it("normalizes string and object blocking issues", () => {
    const issues = normalizeBlockingIssues([
      "bad",
      { code: "X", path: "$.x", severity: "warning", message: "warn" },
    ])
    assert.equal(issues.length, 2)
    assert.equal(issues[0]?.code, "BLOCKING_ISSUE")
    assert.equal(issues[1]?.code, "X")
  })

  it("evaluates deployability from severities", () => {
    assert.equal(isDeployable([]), true)
    assert.equal(isDeployable([{ code: "W", path: "$.x", severity: "warning", message: "w" }]), true)
    assert.equal(isDeployable([{ code: "E", path: "$.x", severity: "error", message: "e" }]), false)
  })
})
