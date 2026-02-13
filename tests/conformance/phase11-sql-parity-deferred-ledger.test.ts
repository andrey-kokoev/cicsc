import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase11 sql parity deferred ledger", () => {
  it("freezes deferred items with explicit closure strategies", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase11-sql-parity-deferred-ledger.json")
    const doc = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(doc.version, "cicsc/phase11-sql-parity-deferred-ledger-v1")
    assert.ok(Array.isArray(doc.items))
    assert.ok(doc.items.length >= 2)
    for (const i of doc.items) {
      assert.equal(typeof i.id, "string")
      assert.equal(typeof i.closure_strategy, "string")
      assert.equal(typeof i.owner, "string")
      assert.match(i.target_date, /^\d{4}-\d{2}-\d{2}$/)
    }
  })
})
