import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"

describe("Kanban v1 reference spec", () => {
  it("compiles with lanes, WIP, swimlanes, and policies", () => {
    const raw = readFileSync(join(process.cwd(), "verticals/kanban/spec.v1.json"), "utf8")
    const spec = JSON.parse(raw)
    const bundle = compileSpecToBundleV0(spec)
    assert.ok((bundle.core_ir.types as any).Card)
    assert.ok((bundle.core_ir.policies as any).can_move_card)
    assert.ok((bundle.core_ir.constraints as any).wip_in_progress_limit)
    assert.ok((bundle.core_ir.views as any).board)
  })
})
