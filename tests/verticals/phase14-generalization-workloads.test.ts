import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase14 generalization workloads", () => {
  it("records pass suite for required workload gates", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase14-generalization-workloads.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase14-generalization-workloads-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.category_model_conformance.status, "pass")
    assert.equal(r.checks.parity_envelope_differentials.status, "pass")
    assert.equal(r.checks.hardening_closure_report.status, "pass")
  })
})
