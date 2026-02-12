import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"

describe("Ticketing v1 vertical spec", () => {
  it("compiles the Ticketing v1 vertical spec to Core IR", () => {
    const raw = readFileSync(join(process.cwd(), "verticals/ticketing/spec.v1.json"), "utf8")
    const spec = JSON.parse(raw)
    const bundle = compileSpecToBundleV0(spec)
    assert.equal(bundle.core_ir.version, 0)
    assert.ok((bundle.core_ir.types as any).Ticket)
    assert.ok((bundle.core_ir.slas as any).first_response)
    assert.ok((bundle.core_ir.slas as any).time_to_resolution)
  })
})
