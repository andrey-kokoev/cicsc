import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase12 domain matrix", () => {
  it("freezes expanded domains and workload gate contract", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase12-domain-matrix.json")
    const doc = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(doc.version, "cicsc/phase12-domain-matrix-v1")
    assert.ok(Array.isArray(doc.domains))
    assert.ok(doc.domains.length >= 4)
    for (const d of doc.domains) {
      assert.equal(typeof d.id, "string")
      assert.equal(typeof d.tenants, "number")
      assert.equal(typeof d.workload, "string")
    }
    assert.ok(Array.isArray(doc.workload_contract.required_gates))
    assert.ok(doc.workload_contract.required_gates.length >= 3)
  })
})
