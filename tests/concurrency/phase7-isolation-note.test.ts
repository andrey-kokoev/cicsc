import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase7 isolation normative note", () => {
  it("references strengthened phase7 evidence while preserving exclusions", () => {
    const p = path.resolve(process.cwd(), "docs/spec/isolation-guarantees.md")
    const note = fs.readFileSync(p, "utf8")

    assert.equal(note.includes("Phase 7 Scoped"), true)
    assert.equal(note.includes("phase7-concurrency-contract-delta.json"), true)
    assert.equal(note.includes("phase7-concurrency-adversarial.json"), true)
    assert.equal(note.includes("phase7-isolation-differential.json"), true)
    assert.equal(note.includes("Explicit Scoped Exclusions"), true)
    assert.equal(note.includes("No distributed transaction guarantee."), true)
  })
})
