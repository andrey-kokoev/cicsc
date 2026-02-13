import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase14 operator-readiness matrix", () => {
  it("freezes runbook, slo, and diagnostics readiness scope", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase14-operator-readiness-matrix.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase14-operator-readiness-matrix-v1")
    assert.equal(r.items.length, 3)
    const ids = new Set((r.items ?? []).map((x: any) => x.id))
    assert.ok(ids.has("runbook_completeness"))
    assert.ok(ids.has("slo_alert_readiness"))
    assert.ok(ids.has("diagnostic_bundle_readiness"))
    assert.equal(r.policy.must_have_executable_evidence, true)
  })
})
