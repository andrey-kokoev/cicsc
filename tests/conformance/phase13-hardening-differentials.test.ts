import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase13 hardening differentials", () => {
  it("records pass differential coverage for hardening matrix", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase13-hardening-differentials.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase13-hardening-differentials-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.post_cutover_diff.status, "pass")
    assert.equal(r.checks.parity_envelope_diff.status, "pass")
    assert.equal(r.checks.category_model_guard.status, "pass")
  })
})
