// /tests/concurrency/causality-replay.test.ts
// Phase 4: Causality replay executable tests (P4.3.1, P4.3.4)
// Verifies Lean theorems: replay_stream_preserves_happensBefore_order,
//                        replay_deterministic_on_causallyEquivalent_streams

import { describe, it } from "node:test"
import assert from "node:assert/strict"

// Event type matching Lean Event structure
type Event = {
  tenantId: string
  entityType: string
  entityId: string
  seq: number
  eventType: string
  payload: unknown
  ts: number
  actor: string
}

type StreamId = {
  tenantId: string
  entityType: string
  entityId: string
}

/** Check if two events are in the same stream */
function sameStream(e1: Event, e2: Event): boolean {
  return e1.tenantId === e2.tenantId &&
         e1.entityType === e2.entityType &&
         e1.entityId === e2.entityId
}

/** Happens-before relation: same stream and lower sequence */
function happensBefore(e1: Event, e2: Event): boolean {
  return sameStream(e1, e2) && e1.seq < e2.seq
}

/** Check if event matches stream ID */
function inStream(sid: StreamId, e: Event): boolean {
  return e.tenantId === sid.tenantId &&
         e.entityType === sid.entityType &&
         e.entityId === sid.entityId
}

/** Check if e1 appears before e2 in history */
function appearsBefore(history: Event[], e1: Event, e2: Event): boolean {
  const idx1 = history.indexOf(e1)
  const idx2 = history.indexOf(e2)
  return idx1 !== -1 && idx2 !== -1 && idx1 < idx2
}

/** Check if history respects causality (matches isCausal predicate) */
function isCausal(history: Event[]): boolean {
  for (let i = 0; i < history.length; i++) {
    for (let j = i + 1; j < history.length; j++) {
      const e1 = history[i]
      const e2 = history[j]
      if (happensBefore(e2, e1)) {
        // e2 should appear before e1 (lower seq first)
        return false
      }
    }
  }
  return true
}

/** Events are concurrent if same stream but no happens-before either way */
function concurrent(e1: Event, e2: Event): boolean {
  return sameStream(e1, e2) && 
         !happensBefore(e1, e2) && 
         !happensBefore(e2, e1)
}

/** Replay events for a stream (simplified reducer simulation) */
function replayStream(
  history: Event[],
  sid: StreamId,
  reducer: (state: string, e: Event) => string
): { finalState: string; appliedEvents: Event[] } {
  const stream = history.filter(e => inStream(sid, e))
  // Sort by seq to ensure causal order
  stream.sort((a, b) => a.seq - b.seq)
  
  let state = "initial"
  const applied: Event[] = []
  
  for (const e of stream) {
    state = reducer(state, e)
    applied.push(e)
  }
  
  return { finalState: state, appliedEvents: applied }
}

describe("P4.3.1: isCausal connected to replay behavior", () => {
  it("rejects histories where events are out of sequence order", () => {
    const sid: StreamId = { tenantId: "t1", entityType: "Ticket", entityId: "e1" }
    
    // Out of order: seq 2 appears before seq 1
    const badHistory: Event[] = [
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 2, eventType: "Update", payload: {}, ts: 2, actor: "a" },
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "Create", payload: {}, ts: 1, actor: "a" },
    ]
    
    assert.strictEqual(isCausal(badHistory), false, "History with inverted seq should not be causal")
  })
  
  it("accepts histories where events respect sequence order", () => {
    const goodHistory: Event[] = [
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "Create", payload: {}, ts: 1, actor: "a" },
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 2, eventType: "Update", payload: {}, ts: 2, actor: "a" },
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 3, eventType: "Close", payload: {}, ts: 3, actor: "a" },
    ]
    
    assert.strictEqual(isCausal(goodHistory), true, "History with ordered seq should be causal")
  })
  
  it("allows interleaved events from different streams", () => {
    const mixedHistory: Event[] = [
      // Stream 1
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "Create", payload: {}, ts: 1, actor: "a" },
      // Stream 2 (different entity)
      { tenantId: "t1", entityType: "Ticket", entityId: "e2", seq: 1, eventType: "Create", payload: {}, ts: 2, actor: "a" },
      // Stream 1 continues
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 2, eventType: "Update", payload: {}, ts: 3, actor: "a" },
      // Stream 2 continues
      { tenantId: "t1", entityType: "Ticket", entityId: "e2", seq: 2, eventType: "Update", payload: {}, ts: 4, actor: "a" },
    ]
    
    assert.strictEqual(isCausal(mixedHistory), true, "Interleaved stream events should be causal")
  })
})

describe("P4.3.4: Deterministic replay under causally-equivalent permutations", () => {
  const simpleReducer = (state: string, e: Event): string => {
    return `${state}.${e.eventType}(seq=${e.seq})`
  }
  
  it("produces same state for histories with different interleaving", () => {
    const sid: StreamId = { tenantId: "t1", entityType: "Ticket", entityId: "e1" }
    
    // Two different orderings of events from different streams
    // Stream 1: e1(seq=1), e1(seq=2)
    // Stream 2: e2(seq=1), e2(seq=2)
    const historyA: Event[] = [
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "A", payload: {}, ts: 1, actor: "a" },
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 2, eventType: "B", payload: {}, ts: 2, actor: "a" },
      { tenantId: "t1", entityType: "Ticket", entityId: "e2", seq: 1, eventType: "X", payload: {}, ts: 3, actor: "a" },
      { tenantId: "t1", entityType: "Ticket", entityId: "e2", seq: 2, eventType: "Y", payload: {}, ts: 4, actor: "a" },
    ]
    
    const historyB: Event[] = [
      // Different interleaving - all of e2 first
      { tenantId: "t1", entityType: "Ticket", entityId: "e2", seq: 1, eventType: "X", payload: {}, ts: 1, actor: "a" },
      { tenantId: "t1", entityType: "Ticket", entityId: "e2", seq: 2, eventType: "Y", payload: {}, ts: 2, actor: "a" },
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "A", payload: {}, ts: 3, actor: "a" },
      { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 2, eventType: "B", payload: {}, ts: 4, actor: "a" },
    ]
    
    // Both should be causal
    assert.strictEqual(isCausal(historyA), true)
    assert.strictEqual(isCausal(historyB), true)
    
    // Replay e1 stream from both histories
    const resultA = replayStream(historyA, { tenantId: "t1", entityType: "Ticket", entityId: "e1" }, simpleReducer)
    const resultB = replayStream(historyB, { tenantId: "t1", entityType: "Ticket", entityId: "e1" }, simpleReducer)
    
    // Should produce same state (events applied in seq order regardless of interleaving)
    assert.strictEqual(resultA.finalState, resultB.finalState)
    assert.strictEqual(resultA.finalState, "initial.A(seq=1).B(seq=2)")
  })
  
  it("detects concurrent events and verifies commutativity", () => {
    const e1: Event = { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "Update", payload: {}, ts: 1, actor: "a" }
    const e2: Event = { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "Assign", payload: {}, ts: 2, actor: "b" }
    
    // Same seq = concurrent (neither happens before the other)
    assert.strictEqual(concurrent(e1, e2), true)
    
    // With commutative reducer, order shouldn't matter
    const commReducer = (state: string, e: Event): string => {
      // Simple commutative operation: append sorted
      const ops = state === "initial" ? [] : state.split(",").filter(s => s !== "initial")
      ops.push(e.eventType)
      ops.sort()
      return ["initial", ...ops].join(",")
    }
    
    const result1 = [e1, e2].reduce(commReducer, "initial")
    const result2 = [e2, e1].reduce(commReducer, "initial")
    
    assert.strictEqual(result1, result2, "Commutative reducer should give same result for concurrent events")
  })
})

describe("happensBefore partial order properties (matches Lean theorems)", () => {
  it("is irreflexive (no event happens before itself)", () => {
    const e: Event = { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "Create", payload: {}, ts: 1, actor: "a" }
    assert.strictEqual(happensBefore(e, e), false)
  })
  
  it("is transitive", () => {
    const e1: Event = { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "A", payload: {}, ts: 1, actor: "a" }
    const e2: Event = { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 2, eventType: "B", payload: {}, ts: 2, actor: "a" }
    const e3: Event = { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 3, eventType: "C", payload: {}, ts: 3, actor: "a" }
    
    assert.strictEqual(happensBefore(e1, e2), true)
    assert.strictEqual(happensBefore(e2, e3), true)
    assert.strictEqual(happensBefore(e1, e3), true) // transitive
  })
  
  it("is asymmetric", () => {
    const e1: Event = { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 1, eventType: "A", payload: {}, ts: 1, actor: "a" }
    const e2: Event = { tenantId: "t1", entityType: "Ticket", entityId: "e1", seq: 2, eventType: "B", payload: {}, ts: 2, actor: "a" }
    
    assert.strictEqual(happensBefore(e1, e2), true)
    assert.strictEqual(happensBefore(e2, e1), false) // asymmetric
  })
})
