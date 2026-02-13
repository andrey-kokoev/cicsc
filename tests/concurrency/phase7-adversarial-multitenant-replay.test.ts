import { describe, it } from "node:test"
import assert from "node:assert/strict"

type Event = {
  tenantId: string
  entityType: string
  entityId: string
  seq: number
  eventType: string
}

type StreamId = {
  tenantId: string
  entityType: string
  entityId: string
}

function inStream(sid: StreamId, e: Event): boolean {
  return e.tenantId === sid.tenantId && e.entityType === sid.entityType && e.entityId === sid.entityId
}

function replayEvents(history: Event[], sid: StreamId): string[] {
  return history
    .filter((e) => inStream(sid, e))
    .sort((a, b) => a.seq - b.seq)
    .map((e) => `${e.eventType}#${e.seq}`)
}

describe("phase7 adversarial multi-tenant replay", () => {
  it("preserves tenant separation for same entityType/entityId", () => {
    const history: Event[] = [
      { tenantId: "t1", entityType: "Ticket", entityId: "E-1", seq: 1, eventType: "Create" },
      { tenantId: "t2", entityType: "Ticket", entityId: "E-1", seq: 1, eventType: "Create" },
      { tenantId: "t1", entityType: "Ticket", entityId: "E-1", seq: 2, eventType: "Close" },
      { tenantId: "t2", entityType: "Ticket", entityId: "E-1", seq: 2, eventType: "Assign" },
    ]

    assert.deepEqual(
      replayEvents(history, { tenantId: "t1", entityType: "Ticket", entityId: "E-1" }),
      ["Create#1", "Close#2"]
    )
    assert.deepEqual(
      replayEvents(history, { tenantId: "t2", entityType: "Ticket", entityId: "E-1" }),
      ["Create#1", "Assign#2"]
    )
  })

  it("is deterministic under cross-stream interleaving permutations", () => {
    const a1: Event = { tenantId: "t1", entityType: "Ticket", entityId: "A", seq: 1, eventType: "Create" }
    const a2: Event = { tenantId: "t1", entityType: "Ticket", entityId: "A", seq: 2, eventType: "Close" }
    const b1: Event = { tenantId: "t1", entityType: "Ticket", entityId: "B", seq: 1, eventType: "Create" }
    const b2: Event = { tenantId: "t1", entityType: "Ticket", entityId: "B", seq: 2, eventType: "Assign" }

    const h1 = [a1, b1, a2, b2]
    const h2 = [b1, b2, a1, a2]

    assert.deepEqual(
      replayEvents(h1, { tenantId: "t1", entityType: "Ticket", entityId: "A" }),
      replayEvents(h2, { tenantId: "t1", entityType: "Ticket", entityId: "A" })
    )
    assert.deepEqual(
      replayEvents(h1, { tenantId: "t1", entityType: "Ticket", entityId: "B" }),
      replayEvents(h2, { tenantId: "t1", entityType: "Ticket", entityId: "B" })
    )
  })
})
