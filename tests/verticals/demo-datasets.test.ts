import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"

import { compileSpecToBundleV0 } from "../../runtime/http/compile"
import { verifyHistoryAgainstIr } from "../../core/runtime/verify"
import type { VmIntrinsics } from "../../core/vm/eval"

const intrinsics: VmIntrinsics = {
  has_role: () => true,
  role_of: () => "user",
  auth_ok: () => true,
  constraint: () => true,
  len: () => 0,
  str: (v) => (v == null ? null : String(v)),
  int: () => null,
  float: () => null,
}

const CASES = [
  { spec: "verticals/kanban/spec.v1.json", dataset: "verticals/kanban/demo-dataset.json" },
  { spec: "verticals/ticketing/spec.v1.json", dataset: "verticals/ticketing/demo-dataset.json" },
  { spec: "verticals/crm/spec.v1.json", dataset: "verticals/crm/demo-dataset.json" },
] as const

describe("vertical demo datasets", () => {
  for (const c of CASES) {
    it(`replay-verifies ${c.dataset}`, () => {
      const specRaw = readFileSync(join(process.cwd(), c.spec), "utf8")
      const dataRaw = readFileSync(join(process.cwd(), c.dataset), "utf8")
      const bundle = compileSpecToBundleV0(JSON.parse(specRaw))
      const dataset = JSON.parse(dataRaw)

      const report = verifyHistoryAgainstIr({
        bundle,
        events: dataset.events,
        now: 100,
        actor: "verifier",
        intrinsics,
      })

      assert.equal(report.ok, true)
    })
  }
})
