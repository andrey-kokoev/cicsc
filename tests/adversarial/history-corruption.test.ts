import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { detectHistoryCorruption } from "../../core/runtime/history-integrity"
import { hashEventHistory } from "../../core/runtime/history-hash"
import type { Event } from "../../core/runtime/replay"

describe("history corruption detection", () => {
  it("detects missing sequence numbers in stream", () => {
    const events: Event[] = [
      { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 1, event_type: "created", payload: {}, ts: 1, actor_id: "u" },
      { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 3, event_type: "closed", payload: {}, ts: 2, actor_id: "u" },
    ]

    const out = detectHistoryCorruption({ events })
    assert.ok(out.some((x) => x.kind === "SEQ_GAP"))
  })

  it("detects tampered event history by hash mismatch", () => {
    const clean: Event[] = [
      { tenant_id: "t", entity_type: "Ticket", entity_id: "A", seq: 1, event_type: "created", payload: { n: 1 }, ts: 1, actor_id: "u" },
    ]
    const expectedHash = hashEventHistory(clean)

    const tampered: Event[] = [
      { ...clean[0]!, payload: { n: 999 } },
    ]

    const out = detectHistoryCorruption({ events: tampered, expected_hash: expectedHash })
    assert.ok(out.some((x) => x.kind === "HASH_MISMATCH"))
  })
})
