import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { KernelMemoryBackend } from "../../kernel/src/memory-backend"

describe("kernel memory backend", () => {
  it("stores and returns events in stable stream order", () => {
    const b = new KernelMemoryBackend()
    b.append([
      { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 2, event_type: "x", payload: {}, ts: 2, actor_id: "u" } as any,
      { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 1, event_type: "x", payload: {}, ts: 1, actor_id: "u" } as any,
    ])

    const out = b.readAll()
    assert.deepEqual(out.map((e) => e.seq), [1, 2])
  })
})
