import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { readFileSync } from "node:fs"
import { join } from "node:path"

const FILES = [
  "verticals/kanban/migration.v0_to_v1.json",
  "verticals/ticketing/migration.v0_to_v1.json",
  "verticals/crm/migration.v0_to_v1.json",
] as const

describe("vertical migration examples", () => {
  for (const rel of FILES) {
    it(`contains minimal v0->v1 migration: ${rel}`, () => {
      const raw = readFileSync(join(process.cwd(), rel), "utf8")
      const doc = JSON.parse(raw)
      const migName = Object.keys(doc.migrations ?? {})[0]
      assert.ok(migName)
      const m = doc.migrations[migName]
      assert.equal(m.from, 0)
      assert.equal(m.to, 1)
      assert.equal(typeof m.entity, "string")
      assert.ok(Object.keys(m.event_transforms ?? {}).length > 0)
      assert.ok(Object.keys(m.state_map ?? {}).length > 0)
    })
  }
})
