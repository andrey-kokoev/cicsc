import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase5 incident register", () => {
  it("captures severity-labeled drift/perf/missing-primitive incidents", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase5-ticketing-incidents.json")
    const reg = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(reg.version, "cicsc/phase5-incident-register-v1")
    assert.equal(reg.vertical, "ticketing")
    assert.ok(Array.isArray(reg.incidents))
    assert.ok(reg.incidents.length >= 3)

    const cats = new Set(reg.incidents.map((i: any) => i.category))
    assert.equal(cats.has("missing_primitive"), true)
    assert.equal(cats.has("drift_risk"), true)
    assert.equal(cats.has("perf_visibility"), true)

    for (const i of reg.incidents) {
      assert.ok(["high", "medium", "low"].includes(i.severity))
    }
  })
})
