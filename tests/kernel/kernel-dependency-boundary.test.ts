import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"

describe("kernel dependency boundary", () => {
  it("does not import HTTP/worker/SQL adapter layers", () => {
    const src = readFileSync(join(process.cwd(), "kernel/src/index.ts"), "utf8")
    const forbidden = [
      "/runtime/http/",
      "/runtime/db/",
      "/adapters/sqlite/",
      "/adapters/postgres/",
      "worker",
      "d1",
      "sql",
    ]

    for (const token of forbidden) {
      assert.equal(src.toLowerCase().includes(token), false, `kernel import leak detected: ${token}`)
    }
  })
})
