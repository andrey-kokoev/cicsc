import type { Event } from "./replay"

export type SnapshotCompactionPlan = {
  should_compact: boolean
  reason?: "event_count" | "time_window"
  up_to_seq?: number
}

export function planSnapshotCompaction (params: {
  events: Event[]
  last_snapshot_seq: number
  min_events_since_snapshot: number
  max_interval_seconds: number
}): SnapshotCompactionPlan {
  const events = [...params.events].sort((a, b) => a.seq - b.seq || a.ts - b.ts)
  const pending = events.filter((e) => e.seq > params.last_snapshot_seq)
  if (pending.length === 0) return { should_compact: false }

  const firstTs = pending[0]!.ts
  const lastTs = pending[pending.length - 1]!.ts

  if (pending.length >= params.min_events_since_snapshot) {
    return {
      should_compact: true,
      reason: "event_count",
      up_to_seq: pending[pending.length - 1]!.seq,
    }
  }

  if (lastTs - firstTs >= params.max_interval_seconds) {
    return {
      should_compact: true,
      reason: "time_window",
      up_to_seq: pending[pending.length - 1]!.seq,
    }
  }

  return { should_compact: false }
}
