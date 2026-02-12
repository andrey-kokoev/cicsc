import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"

const EXAMPLES = [
  "docs/examples/kanban/spec.v0.json",
  "docs/examples/ticketing/spec.v0.json",
  "docs/examples/crm/spec.v0.json",
] as const

describe("spec examples", () => {
  for (const rel of EXAMPLES) {
    it(`compiles ${rel}`, () => {
      const raw = readFileSync(join(process.cwd(), rel), "utf8")
      const spec = JSON.parse(raw)
      const bundle = compileSpecToBundleV0(spec)
      assert.equal(bundle.core_ir.version, 0)
      assert.ok(Object.keys(bundle.core_ir.types ?? {}).length > 0)
    })
  }
})
