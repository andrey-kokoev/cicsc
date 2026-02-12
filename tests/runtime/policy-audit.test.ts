import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { makePolicyChangeAuditRecords } from "../../runtime/audit/policy-changes"

describe("policy change audit trail", () => {
  it("emits add/update/remove audit records for policy changes", () => {
    const records = makePolicyChangeAuditRecords({
      tenant_id: "t",
      actor_id: "admin",
      ts: 10,
      before: {
        version: 0,
        types: {},
        policies: {
          p1: { params: [], expr: { lit: { bool: true } } },
          p2: { params: [], expr: { lit: { bool: true } } },
        },
      } as any,
      after: {
        version: 0,
        types: {},
        policies: {
          p1: { params: [], expr: { lit: { bool: false } } },
          p3: { params: [], expr: { lit: { bool: true } } },
        },
      } as any,
    })

    const actions = records.map((r) => (r.payload as any).action).sort()
    assert.deepEqual(actions, ["policy_added", "policy_removed", "policy_updated"])
  })
})
