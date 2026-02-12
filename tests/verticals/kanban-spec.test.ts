import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"

describe("Kanban vertical spec", () => {
  it("compiles the Kanban vertical spec to Core IR", () => {
    const raw = readFileSync(join(process.cwd(), "verticals/kanban/spec.v0.json"), "utf8")
    const spec = JSON.parse(raw)
    const bundle = compileSpecToBundleV0(spec)
    assert.equal(bundle.core_ir.version, 0)
    assert.ok((bundle.core_ir.types as any).Card)
    assert.ok((bundle.core_ir.constraints as any).wip_in_progress_limit)
  })
})
