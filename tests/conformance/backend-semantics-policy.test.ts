import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("backend semantics policy contract", () => {
  it("declares sqlite/postgres/oracle null-ordering and collation policy deltas", () => {
    const p = path.resolve(process.cwd(), "tests/conformance/backend-semantics-policy.json")
    const policy = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(policy.version, "cicsc/backend-semantics-policy-v1")
    assert.equal(policy.canonical_comparison.mode, "oracle_normalized")
    assert.ok(policy.semantics?.sqlite)
    assert.ok(policy.semantics?.postgres)
    assert.ok(policy.semantics?.oracle_interpreter)
    assert.ok(Array.isArray(policy.known_deltas))
    assert.ok(policy.known_deltas.length >= 2)
    assert.equal(policy.alignment_policy.order_by, "always_generate_explicit_order_by_for_deterministic_queries")
  })
})
