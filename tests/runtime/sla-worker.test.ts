import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { runSlaEvaluationSweep } from "../../runtime/sla/worker"

describe("background SLA evaluation worker", () => {
  it("marks overdue SLA rows as breached", async () => {
    const marked: string[] = []
    const dueRows = [
      { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "A" },
      { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "B" },
    ]

    const out = await runSlaEvaluationSweep({
      store: {
        adapter: {
          async sla_check_due () {
            return dueRows
          },
          async sla_mark_breached (p) {
            marked.push(`${p.name}:${p.entity_id}`)
          },
        },
      },
      tenant_id: "t",
      sla_names: ["response"],
      now: 100,
    })

    assert.equal(out.scanned, 2)
    assert.equal(out.marked_breached, 2)
    assert.deepEqual(marked.sort(), ["response:A", "response:B"])
  })
})
