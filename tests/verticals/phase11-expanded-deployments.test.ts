import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase11 expanded deployments", () => {
  it("freezes deployment set and workload contract", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase11-expanded-deployments.json")
    const doc = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(doc.version, "cicsc/phase11-expanded-deployments-v1")
    assert.ok(Array.isArray(doc.deployments))
    assert.ok(doc.deployments.length >= 3)
    for (const d of doc.deployments) {
      assert.equal(typeof d.id, "string")
      assert.equal(typeof d.vertical, "string")
      assert.equal(typeof d.tenant_count, "number")
    }
    assert.ok(Array.isArray(doc.workload_contract.required_gates))
    assert.ok(doc.workload_contract.required_gates.length >= 3)
  })
})
