import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase6 isolation/concurrency normative note", () => {
  it("documents scoped exclusions aligned with the phase6 contract", () => {
    const p = path.resolve(process.cwd(), "docs/spec/isolation-guarantees.md")
    const note = fs.readFileSync(p, "utf8")

    assert.equal(note.includes("phase6-concurrency-contract.json"), true)
    assert.equal(note.includes("Explicit Scoped Exclusions"), true)
    assert.equal(note.includes("No distributed transaction guarantee."), true)
    assert.equal(note.includes("No backend lock-manager equivalence claim."), true)
  })
})
