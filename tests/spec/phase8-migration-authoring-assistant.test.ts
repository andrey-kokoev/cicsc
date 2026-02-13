import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase8 migration authoring assistant report", () => {
  it("records green coverage/safety/rollback readiness checks", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase8-migration-authoring-assistant.json")
    const r = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(r.version, "cicsc/phase8-migration-authoring-assistant-v1")
    assert.equal(r.overall, "pass")
    assert.equal(r.checks.migration_totality.status, "pass")
    assert.equal(r.checks.migration_spec_shape.status, "pass")
    assert.equal(r.checks.rollback_readiness.status, "pass")
  })
})
