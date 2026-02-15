# Phase BQ: Event Transform Fan-out

**Status**: PLANNED (v1.6.0)  
**Agent**: AGENT_GEMINI  
**Vertical Gap**: Migration one-to-one limitation

## Problem

Current migration transforms are 1-to-1:
```typescript
// Current: One old event → one new event
EventV1.OrderCreated → EventV2.OrderCreated
```

Vertical evolution needs 1-to-many:
```typescript
// Needed: One old event → multiple new events
EventV1.OrderCreated → [
  EventV2.OrderCreated,
  EventV2.InventoryReserved,
  EventV2.PaymentAuthorized
]
```

## Core IR Extension

```typescript
export type EventTransformV0 = {
  // Existing
  emit_as?: string
  payload_map?: Record<string, ExprV0>
  drop?: boolean
  
  // NEW: Fan-out
  emit_many?: {
    events: Array<{
      event_type: string
      payload: Record<string, ExprV0>
      condition?: ExprV0  // Optional filter
    }>
  }
}
```

## Spec DSL

```python
migrations {
  from_version: 1
  to_version: 2
  
  event_transform OrderCreated {
    // Fan out to multiple events
    emit_many: [
      {
        event_type: "OrderCreatedV2"
        payload: { id, customer, total }
      }
      {
        event_type: "InventoryReserved"
        payload: { order_id: id, items: items }
        condition: items.length > 0
      }
      {
        event_type: "PaymentAuthorized"
        payload: { order_id: id, amount: total }
        condition: total > 0
      }
    ]
  }
}
```

## Milestones

### BQ1: Core IR Extension
- [x] BQ1.1: Add emit_many to EventTransformV0
- [x] BQ1.2: Define fan-out expression context
- [x] BQ1.3: Update IR validator
- [x] BQ1.4: Spec DSL syntax

### BQ2: Migration Engine
- [x] BQ2.1: Handle multiple output events
- [x] BQ2.2: Preserve event ordering
- [x] BQ2.3: Idempotency
- [x] BQ2.4: Replay verification

## Worktree Assignment

**Worktree**: `worktrees/gemini`  
**Branch**: `gemini`  
**Agent**: AGENT_GEMINI
