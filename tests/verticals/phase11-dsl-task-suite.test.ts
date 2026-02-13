import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import path from "node:path"

describe("phase11 dsl task suite", () => {
  it("defines non-programmer tasks with objective rubric", () => {
    const p = path.resolve(process.cwd(), "docs/pilot/phase11-dsl-task-suite.json")
    const doc = JSON.parse(fs.readFileSync(p, "utf8"))

    assert.equal(doc.version, "cicsc/phase11-dsl-task-suite-v1")
    assert.equal(doc.cohort, "non_programmer")
    assert.ok(Array.isArray(doc.tasks))
    assert.ok(doc.tasks.length >= 3)
    for (const t of doc.tasks) {
      assert.equal(typeof t.id, "string")
      assert.ok(Array.isArray(t.success_criteria))
      assert.ok(t.success_criteria.length >= 3)
      assert.equal(typeof t.max_minutes, "number")
    }
    assert.equal(typeof doc.rubric.task_pass_threshold, "number")
    assert.equal(typeof doc.rubric.cohort_pass_threshold, "number")
    assert.ok(Array.isArray(doc.rubric.required_metrics))
  })
})
