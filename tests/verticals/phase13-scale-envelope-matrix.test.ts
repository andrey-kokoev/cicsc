import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase13 scale envelope matrix", () => {
  it("freezes scale envelope and workload contract", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase13-scale-envelope-matrix.json")
    const d = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(d.version, "cicsc/phase13-scale-envelope-matrix-v1")
    assert.ok(Array.isArray(d.envelope))
    assert.ok(d.envelope.length >= 4)
    for (const e of d.envelope) {
      assert.equal(typeof e.id, "string")
      assert.equal(typeof e.tenant_count, "number")
      assert.equal(typeof e.concurrency_level, "number")
    }
  })
})
