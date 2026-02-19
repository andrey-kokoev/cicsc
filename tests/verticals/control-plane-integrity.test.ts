import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import fs from "node:fs"
import path from "node:path"

const ROOT = process.cwd()

describe("control-plane integrity", () => {
  it("prints a non-empty gate execution plan", () => {
    const run = spawnSync("./scripts/run_gate_model.sh", ["--print-plan"], {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)

    const plan = JSON.parse(run.stdout)
    assert.ok(Array.isArray(plan.steps) && plan.steps.length > 0)
    const gateIds = new Set((plan.steps ?? []).map((step: any) => step.gate_id))
    assert.equal(gateIds.has("GATE_COLLAB_SURFACE_COHERENCY"), true)
    assert.equal(gateIds.has("GATE_DB_PROTOCOL_SURFACE"), true)

    for (const step of plan.steps ?? []) {
      assert.equal(typeof step.gate_id, "string")
      assert.equal(typeof step.script, "string")
      assert.ok(step.script.startsWith("scripts/"))
    }
  })

  it("gate-model execution plan runs successfully", () => {
    const planRun = spawnSync("./scripts/run_gate_model.sh", ["--print-plan"], {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(planRun.status, 0, planRun.stderr || planRun.stdout)

    const execRun = spawnSync("./scripts/run_gate_model.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(execRun.status, 0, execRun.stderr || execRun.stdout)
  })

  it("canonical gate entrypoint delegates directly to run_gate_model", () => {
    const gateScript = fs.readFileSync(path.join(ROOT, "control-plane/check_gates.sh"), "utf8")
    assert.match(gateScript, /run_gate_model\.sh/)
    assert.doesNotMatch(gateScript, /check_canonical_execution_model\.sh/)
  })

  it("removed collaboration wrappers are absent", () => {
    assert.equal(fs.existsSync(path.join(ROOT, "scripts", "check_canonical_execution_model.sh")), false)
    assert.equal(fs.existsSync(path.join(ROOT, "scripts", "check_status_projection_sync.sh")), false)
    assert.equal(fs.existsSync(path.join(ROOT, "scripts", "check_execution_structure_roundtrip.sh")), false)
    assert.equal(fs.existsSync(path.join(ROOT, "scripts", "check_execution_structure_roundtrip_ledger.sh")), false)
    assert.equal(fs.existsSync(path.join(ROOT, "control-plane", "scripts", "export_execution_status.py")), false)
    assert.equal(fs.existsSync(path.join(ROOT, "scripts", "check_collaboration_model.sh")), false)
  })
})
