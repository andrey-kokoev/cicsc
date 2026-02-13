import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 expanded conflict matrix", () => {
  it("covers expanded deterministic outcome cases", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-conflict-matrix-expanded.json")
    const matrix = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(matrix.version, "cicsc/phase7-conflict-matrix-expanded-v1")
    assert.equal(matrix.cases.length, 6)
    const ids = new Set<string>(matrix.cases.map((c: any) => c.id))
    assert.equal(ids.has("same_stream_write_write"), true)
    assert.equal(ids.has("cross_stream_independent"), true)
    assert.equal(ids.has("cross_tenant_same_entity_key"), true)
    assert.equal(ids.has("duplicate_command_idempotency"), true)
  })
})
