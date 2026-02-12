import type { Event } from "./replay"
import { hashEventHistory } from "./history-hash"

export type HistoryCorruption = {
  kind: "SEQ_GAP" | "SEQ_REGRESSION" | "HASH_MISMATCH"
  stream: string
  message: string
}

export function detectHistoryCorruption (params: {
  events: Event[]
  expected_hash?: string
}): HistoryCorruption[] {
  const out: HistoryCorruption[] = []
  const groups = new Map<string, Event[]>()

  for (const e of params.events) {
    const key = `${e.tenant_id}|${e.entity_type}|${e.entity_id}`
    const arr = groups.get(key)
    if (arr) arr.push(e)
    else groups.set(key, [e])
  }

  for (const [stream, arr] of groups.entries()) {
    const xs = [...arr].sort((a, b) => a.seq - b.seq || a.ts - b.ts)
    let expected = 1
    for (const e of xs) {
      if (e.seq < expected) {
        out.push({
          kind: "SEQ_REGRESSION",
          stream,
          message: `sequence regressed at seq=${e.seq}; expected >= ${expected}`,
        })
      } else if (e.seq > expected) {
        out.push({
          kind: "SEQ_GAP",
          stream,
          message: `missing sequence: expected ${expected}, got ${e.seq}`,
        })
        expected = e.seq + 1
      } else {
        expected++
      }
    }
  }

  if (params.expected_hash) {
    const got = hashEventHistory(params.events)
    if (got !== params.expected_hash) {
      out.push({
        kind: "HASH_MISMATCH",
        stream: "*",
        message: `history hash mismatch: expected ${params.expected_hash}, got ${got}`,
      })
    }
  }

  return out
}
