import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 proven-vs-experimental feature gating", () => {
  it("declares both proven and experimental surfaces", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-feature-gates.json")
    const gates = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(gates.version, "cicsc/phase6-feature-gates-v1")
    assert.ok(Array.isArray(gates.proven))
    assert.ok(Array.isArray(gates.experimental))
    assert.equal(gates.proven.includes("verify"), true)
    assert.equal(gates.experimental.includes("distributed transaction orchestration"), true)
  })

  it("marks OpenAPI surface with feature-gate extension block", () => {
    const p = path.resolve(process.cwd(), "docs/openapi/runtime.yaml")
    const openapi = fs.readFileSync(p, "utf8")
    assert.equal(openapi.includes("x-cicsc-feature-gates:"), true)
    assert.equal(openapi.includes("proven_paths:"), true)
  })
})
