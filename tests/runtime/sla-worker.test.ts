import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { runSlaEvaluationSweep } from "../../runtime/sla/worker"
import type { CoreIrV0 } from "../../core/ir/types"

describe("background SLA evaluation worker", () => {
  it("marks overdue SLA rows as breached", async () => {
    const marked: string[] = []
    const dueRows = [
      { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "A" },
      { tenant_id: "t", name: "response", entity_type: "Ticket", entity_id: "B" },
    ]

    const mockIr: CoreIrV0 = {
      version: 0,
      types: {},
      slas: {
        response: {
          name: "response",
          on_type: "Ticket",
          start: { event: { name: "created" } },
          stop: { event: { name: "responded" } },
          within_seconds: 3600,
          enforce: { none: true },
        }
      }
    }

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
      ir: mockIr,
      tenant_id: "t",
      sla_names: ["response"],
      now: 100,
    })

    assert.equal(out.scanned, 2)
    assert.equal(out.marked_breached, 2)
    assert.deepEqual(marked.sort(), ["response:A", "response:B"])
  })
})
