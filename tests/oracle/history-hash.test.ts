import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { hashEventHistory, hashSnapshots, hashTenantState } from "../../core/runtime/history-hash"
import type { Event } from "../../core/runtime/replay"

describe("history hashing", () => {
  it("is deterministic regardless of event input ordering", () => {
    const a: Event[] = [
      { tenant_id: "t", entity_type: "Ticket", entity_id: "b", seq: 1, event_type: "created", payload: {}, ts: 2, actor_id: "u" },
      { tenant_id: "t", entity_type: "Ticket", entity_id: "a", seq: 1, event_type: "created", payload: {}, ts: 1, actor_id: "u" },
    ]
    const b: Event[] = [...a].reverse()

    assert.equal(hashEventHistory(a), hashEventHistory(b))
  })

  it("changes hash when snapshot content changes", () => {
    const h1 = hashSnapshots([{ entity_id: "a", state: "new" }])
    const h2 = hashSnapshots([{ entity_id: "a", state: "done" }])
    assert.notEqual(h1, h2)
  })

  it("returns component and combined hashes", () => {
    const out = hashTenantState({
      events: [
        { tenant_id: "t", entity_type: "Ticket", entity_id: "a", seq: 1, event_type: "created", payload: {}, ts: 1, actor_id: "u" },
      ],
      snapshots: [{ entity_id: "a", state: "new" }],
    })
    assert.equal(typeof out.events_hash, "string")
    assert.equal(typeof out.snapshots_hash, "string")
    assert.equal(typeof out.combined_hash, "string")
    assert.equal(out.events_hash.length, 64)
    assert.equal(out.snapshots_hash.length, 64)
    assert.equal(out.combined_hash.length, 64)
  })
})
