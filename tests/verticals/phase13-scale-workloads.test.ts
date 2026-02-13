import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase13 scale workloads", () => {
  it("records pass suite for scale workload checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase13-scale-workloads.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase13-scale-workloads-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.multi_domain_workloads.status, "pass")
    assert.equal(r.checks.parity_envelope_differentials.status, "pass")
    assert.equal(r.checks.category_model_conformance.status, "pass")
  })
})
