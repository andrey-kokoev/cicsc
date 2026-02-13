import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"

describe("reference vertical spec usability", () => {
  it("compiles ticketing Spec DSL surface without IR-shaped authoring", () => {
    const specPath = path.resolve(process.cwd(), "verticals/ticketing/spec.v1.json")
    const spec = JSON.parse(fs.readFileSync(specPath, "utf8"))

    assert.ok(spec.entities)
    assert.equal(spec.types, undefined)

    const bundle = compileSpecToBundleV0(spec)
    assert.ok(bundle.core_ir?.types?.Ticket)
  })
})
