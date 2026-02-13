import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase15 deferred-surface matrix", () => {
  it("freezes deferred-surface closure scope and policy", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase15-deferred-surface-matrix.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase15-deferred-surface-matrix-v1")
    assert.equal(r.items.length, 3)
    assert.equal(r.policy.must_have_executable_evidence, true)
    assert.equal(r.policy.deferred_requires_owner_date, true)
    assert.equal(r.policy.no_silent_scope_expansion, true)
  })
})
