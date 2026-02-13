import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"

import { compileSpecV0ToCoreIr } from "../../spec/compile-to-ir"

describe("spec dsl v1 freeze contract", () => {
  it("keeps canonical desugaring output stable for frozen fixture", () => {
    const fixture = JSON.parse(readFileSync("spec/contracts/spec-dsl-v1.fixture.json", "utf8"))
    const expectedIr = JSON.parse(readFileSync("spec/contracts/spec-dsl-v1.ir.json", "utf8"))
    const actualIr = compileSpecV0ToCoreIr(fixture)

    assert.deepEqual(stableJson(actualIr), stableJson(expectedIr))
  })
})

function stableJson<T> (value: T): T {
  return JSON.parse(JSON.stringify(value))
}
