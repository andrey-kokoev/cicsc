import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 comparative incident register", () => {
  it("captures tagged cross-vertical incidents for ticketing and crm", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase6-comparative-incidents.json")
    const reg = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(reg.version, "cicsc/phase6-comparative-incidents-v1")
    assert.deepEqual(reg.verticals, ["ticketing", "crm"])
    assert.ok(Array.isArray(reg.incidents))
    assert.ok(reg.incidents.length >= 3)

    for (const i of reg.incidents) {
      assert.ok(["high", "medium", "low"].includes(i.severity))
      assert.ok(["cross_vertical", "single_vertical"].includes(i.recurrence))
    }

    const recurring = reg.incidents.filter((i: any) => i.recurrence === "cross_vertical")
    assert.ok(recurring.length >= 1)
  })
})
