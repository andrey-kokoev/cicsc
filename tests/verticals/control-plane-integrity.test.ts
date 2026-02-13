import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { spawnSync } from "node:child_process"
import { readFileSync } from "node:fs"
import path from "node:path"

describe("control-plane integrity", () => {
  it("generates tracked views with expected metadata", () => {
    const run = spawnSync("./control-plane/scripts/generate_views.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)

    const phaseIndexPath = path.resolve(process.cwd(), "control-plane/views/phase-index.generated.json")
    const gateOrderPath = path.resolve(process.cwd(), "control-plane/views/gate-order.generated.json")
    const roadmapStatusPath = path.resolve(process.cwd(), "control-plane/views/roadmap-status.generated.json")

    const phaseIndex = JSON.parse(readFileSync(phaseIndexPath, "utf8"))
    const gateOrder = JSON.parse(readFileSync(gateOrderPath, "utf8"))
    const roadmapStatus = JSON.parse(readFileSync(roadmapStatusPath, "utf8"))

    assert.equal(phaseIndex._generated, true)
    assert.equal(gateOrder._generated, true)
    assert.equal(roadmapStatus._generated, true)
    assert.ok(Array.isArray(phaseIndex.phases) && phaseIndex.phases.length > 0)
    assert.ok(Array.isArray(gateOrder.steps) && gateOrder.steps.length > 0)
    assert.ok(Array.isArray(roadmapStatus.rows) && roadmapStatus.rows.length > 0)
  })

  it("gate-model execution plan matches generated gate-order view", () => {
    const planRun = spawnSync("./scripts/run_gate_model.sh", ["--print-plan"], {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(planRun.status, 0, planRun.stderr || planRun.stdout)

    const plan = JSON.parse(planRun.stdout)
    const gateOrderPath = path.resolve(process.cwd(), "control-plane/views/gate-order.generated.json")
    const gateOrder = JSON.parse(readFileSync(gateOrderPath, "utf8"))

    assert.equal(plan.version, "cicsc/gate-model-v1")
    assert.deepEqual(plan.steps, gateOrder.steps)
  })

  it("status projection sync gate passes", () => {
    const run = spawnSync("./scripts/check_status_projection_sync.sh", {
      cwd: process.cwd(),
      encoding: "utf8",
    })
    assert.equal(run.status, 0, run.stderr || run.stdout)
  })
})
