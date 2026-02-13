import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase9 forced-next roadmap map", () => {
  it("maps every finding to a concrete owner-assigned next task", () => {
    const findingsPath = path.resolve(process.cwd(), "docs/pilot/phase9-deployment-findings.json")
    const mapPath = path.resolve(process.cwd(), "docs/pilot/phase9-forced-next-roadmap-map.json")
    const findings = JSON.parse(fs.readFileSync(findingsPath, "utf8"))
    const map = JSON.parse(fs.readFileSync(mapPath, "utf8"))

    assert.equal(map.version, "cicsc/phase9-forced-next-roadmap-map-v1")
    const sourceIds = new Set((findings.findings ?? []).map((f: any) => f.id))
    const mapped = map.tasks ?? []
    assert.ok(mapped.length >= sourceIds.size)

    const mappedSourceIds = new Set(mapped.map((t: any) => t.source_finding))
    for (const id of sourceIds) {
      assert.ok(mappedSourceIds.has(id), `missing mapping for finding ${id}`)
    }

    for (const t of mapped) {
      assert.equal(typeof t.task_id, "string")
      assert.equal(typeof t.owner, "string")
      assert.ok(["low", "medium", "high", "critical"].includes(t.severity))
    }
  })
})
