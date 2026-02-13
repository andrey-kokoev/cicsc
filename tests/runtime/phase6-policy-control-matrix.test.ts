import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

function canRoleExecute(matrix: any, actionName: string, role: string): boolean {
  const action = (matrix.actions ?? []).find((a: any) => a.name === actionName)
  if (!action) return false
  return (action.allowed_roles ?? []).includes(role)
}

describe("phase6 policy control matrix", () => {
  it("declares policy rows for publish/bind/migrate/verify/gates", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-policy-control-matrix.json")
    const matrix = JSON.parse(fs.readFileSync(p, "utf8"))
    const actionNames = matrix.actions.map((a: any) => a.name)

    assert.equal(matrix.version, "cicsc/phase6-policy-control-matrix-v1")
    assert.deepEqual(actionNames, [
      "publish_bundle",
      "bind_tenant_bundle",
      "run_migration",
      "verify_tenant",
      "run_gates",
    ])
  })

  it("enforces deterministic allow/deny outcomes", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-policy-control-matrix.json")
    const matrix = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(canRoleExecute(matrix, "publish_bundle", "release_manager"), true)
    assert.equal(canRoleExecute(matrix, "publish_bundle", "tenant_operator"), false)
    assert.equal(canRoleExecute(matrix, "bind_tenant_bundle", "tenant_operator"), true)
    assert.equal(canRoleExecute(matrix, "run_migration", "auditor"), false)
    assert.equal(canRoleExecute(matrix, "run_gates", "auditor"), true)
  })
})
