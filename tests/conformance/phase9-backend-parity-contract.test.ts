import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 backend parity contract", () => {
  it("freezes backend scope, deferred classes, and required gate set", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase9-backend-parity-contract.json")
    const contract = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(contract.version, "cicsc/phase9-backend-parity-contract-v1")
    assert.deepEqual(contract.scope.backends, ["sqlite", "postgres", "oracle_interpreter"])
    assert.ok(contract.scope.query_ops.includes("having"))
    assert.ok(contract.scope.deferred.includes("exists"))

    const req = contract.gates?.required_differentials ?? []
    assert.ok(req.includes("sqlite_exec_vs_oracle"))
    assert.ok(req.includes("postgres_exec_vs_oracle"))
    assert.ok(req.includes("cross_backend_diff"))
  })
})
