import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { planSnapshotCompaction } from "../../core/runtime/compaction"
import type { Event } from "../../core/runtime/replay"

function ev (seq: number, ts: number): Event {
  return {
    tenant_id: "t",
    entity_type: "Ticket",
    entity_id: "A",
    seq,
    event_type: "e",
    payload: {},
    ts,
    actor_id: "u",
  }
}

describe("snapshot compaction policy", () => {
  it("triggers compaction by event count", () => {
    const out = planSnapshotCompaction({
      events: [ev(1, 1), ev(2, 2), ev(3, 3)],
      last_snapshot_seq: 0,
      min_events_since_snapshot: 3,
      max_interval_seconds: 100,
    })
    assert.equal(out.should_compact, true)
    assert.equal(out.reason, "event_count")
    assert.equal(out.up_to_seq, 3)
  })

  it("triggers compaction by time window", () => {
    const out = planSnapshotCompaction({
      events: [ev(1, 1), ev(2, 1000)],
      last_snapshot_seq: 0,
      min_events_since_snapshot: 10,
      max_interval_seconds: 300,
    })
    assert.equal(out.should_compact, true)
    assert.equal(out.reason, "time_window")
    assert.equal(out.up_to_seq, 2)
  })

  it("does not compact when thresholds are not met", () => {
    const out = planSnapshotCompaction({
      events: [ev(1, 1), ev(2, 2)],
      last_snapshot_seq: 0,
      min_events_since_snapshot: 10,
      max_interval_seconds: 300,
    })
    assert.equal(out.should_compact, false)
  })
})
