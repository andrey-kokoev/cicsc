import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 concurrency contract", () => {
  it("declares stream guarantees and explicit cross-stream boundaries", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-concurrency-contract.json")
    const contract = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(contract.version, "cicsc/phase6-concurrency-contract-v1")
    assert.deepEqual(contract.supported_model.stream_scope.identity, ["tenantId", "entityType", "entityId"])
    assert.ok(contract.supported_model.stream_scope.guarantees.length >= 3)
    assert.ok(contract.supported_model.cross_stream_scope.boundaries.includes("no distributed transaction guarantee"))
  })
})
