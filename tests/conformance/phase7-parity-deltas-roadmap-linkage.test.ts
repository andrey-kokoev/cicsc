import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 parity delta -> execution-structure linkage", () => {
  it("maps each parity delta id into explicit execution-structure entries", () => {
    const deltaPath = path.resolve(process.cwd(), "docs/pilot/phase7-parity-deltas.json")
    const executionStatusPath = path.resolve(process.cwd(), "control-plane/views/execution-status.generated.json")
    const deltas = JSON.parse(fs.readFileSync(deltaPath, "utf8"))
    const executionStatus = JSON.parse(fs.readFileSync(executionStatusPath, "utf8"))
    const checkboxIds = new Set((executionStatus.rows ?? []).map((r: any) => String(r.checkbox_id)))

    for (const d of deltas.deltas ?? []) {
      assert.ok(d.mapped_roadmap_item, `missing mapped checkbox id for ${d.id}`)
      assert.equal(checkboxIds.has(String(d.mapped_roadmap_item)), true, `missing execution-status mapping for ${d.id}`)
    }
  })
})
