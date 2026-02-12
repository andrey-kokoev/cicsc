import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"

describe("CRM v1 reference spec", () => {
  it("compiles with ownership and conversion metrics", () => {
    const raw = readFileSync(join(process.cwd(), "verticals/crm/spec.v1.json"), "utf8")
    const spec = JSON.parse(raw)
    const bundle = compileSpecToBundleV0(spec)
    assert.ok((bundle.core_ir.types as any).Lead)
    assert.ok((bundle.core_ir.policies as any).can_progress_lead)
    assert.ok((bundle.core_ir.views as any).owner_pipeline)
  })
})
