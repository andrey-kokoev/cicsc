import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { detectInvariantDrift } from "../../core/runtime/invariant-drift"
import type { VerifyReport } from "../../core/runtime/verify"

function report (p: {
  version: number
  violations: Array<{ constraint_id: string; kind: "snapshot" | "bool_query"; on_type: string; message: string }>
}): VerifyReport {
  return {
    ok: p.violations.length === 0,
    core_ir_version: 0,
    types_count: 1,
    events_count: 0,
    entities_count: 0,
    constraints_count: 1,
    violations: p.violations,
    ts: 1,
    version_stamp: {
      active_version: p.version,
      verified_at_ts: 1,
    },
  }
}

describe("invariant drift detection", () => {
  it("flags newly introduced violations across versions", () => {
    const baseline = report({ version: 0, violations: [] })
    const candidate = report({
      version: 1,
      violations: [
        {
          constraint_id: "wip",
          kind: "snapshot",
          on_type: "Ticket",
          message: "limit exceeded",
        },
      ],
    })

    const drift = detectInvariantDrift({ baseline, candidate })
    assert.equal(drift.detected, true)
    assert.equal(drift.from_version, 0)
    assert.equal(drift.to_version, 1)
    assert.equal(drift.newly_violated.length, 1)
  })

  it("does not flag drift when candidate has no new violations", () => {
    const baseline = report({
      version: 0,
      violations: [
        {
          constraint_id: "wip",
          kind: "snapshot",
          on_type: "Ticket",
          message: "limit exceeded",
        },
      ],
    })
    const candidate = report({
      version: 1,
      violations: [
        {
          constraint_id: "wip",
          kind: "snapshot",
          on_type: "Ticket",
          message: "limit exceeded",
        },
      ],
    })

    const drift = detectInvariantDrift({ baseline, candidate })
    assert.equal(drift.detected, false)
    assert.equal(drift.newly_violated.length, 0)
  })
})
