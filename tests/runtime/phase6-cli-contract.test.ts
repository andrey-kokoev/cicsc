import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"
import { spawnSync } from "node:child_process"

describe("phase6 cli contract", () => {
  it("freezes compile/install/migrate/verify/gates command surface", () => {
    const contractPath = path.resolve(process.cwd(), "docs/pilot/phase6-cli-contract.json")
    const contract = JSON.parse(fs.readFileSync(contractPath, "utf8"))
    const names = contract.frozen_commands.map((c: any) => c.name)

    assert.equal(contract.version, "cicsc/phase6-cli-contract-v1")
    assert.deepEqual(names, [
      "compile",
      "install",
      "verify",
      "gates",
      "migration-preflight",
      "migration-dry-run",
      "migration-rollback",
    ])
  })

  it("exposes frozen commands in CLI usage", () => {
    const run = spawnSync(process.execPath, ["cli/cicsc.mjs"], {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0)
    const out = run.stdout

    for (const cmd of [
      "compile",
      "install",
      "verify",
      "gates",
      "migration-preflight",
      "migration-dry-run",
      "migration-rollback",
    ]) {
      assert.equal(out.includes(cmd), true, `missing usage for ${cmd}`)
    }
  })
})
