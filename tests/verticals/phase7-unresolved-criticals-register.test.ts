import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 unresolved criticals register", () => {
  it("requires unresolved criticals empty and deferred items owner/date-scoped", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase7-unresolved-criticals-register.json")
    const reg = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(reg.version, "cicsc/phase7-unresolved-criticals-register-v1")
    assert.deepEqual(reg.unresolved_critical_ids, [])

    for (const e of reg.entries ?? []) {
      if (e.status === "deferred") {
        assert.equal(typeof e.owner, "string")
        assert.equal(typeof e.target_date, "string")
      }
    }
  })
})
