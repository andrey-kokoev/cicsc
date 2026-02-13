import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 production-equivalence scope", () => {
  it("freezes workload envelope and data diversity matrix", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-prod-equivalence-scope.json")
    const scope = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(scope.version, "cicsc/phase8-prod-equivalence-scope-v1")
    assert.equal(scope.workload_envelope.snapshot_rows_per_type.large, 100000)
    assert.ok(scope.workload_envelope.query_classes.includes("group_by_aggregates"))
    assert.ok(scope.data_diversity.collation_profiles.includes("mixed_locale_strings"))
    assert.deepEqual(scope.in_scope_backends, ["sqlite", "postgres", "oracle_interpreter"])
  })
})
