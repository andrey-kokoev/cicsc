import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 operator playbook", () => {
  it("defines rollout, rollback, and incident triage procedures", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-operator-playbook.md")
    const doc = fs.readFileSync(p, "utf8")

    assert.equal(doc.includes("## Rollout (Per Tenant)"), true)
    assert.equal(doc.includes("## Rollback (Per Tenant)"), true)
    assert.equal(doc.includes("## Incident Triage"), true)
    assert.equal(doc.includes("phase6-concurrency-conformance.json"), true)
    assert.equal(doc.includes("phase6-migration-concurrency-drill.json"), true)
  })
})
