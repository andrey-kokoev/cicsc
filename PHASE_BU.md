# Phase BU: Multi-Entity Commands

**Status**: PLANNED (v1.10.0)  
**Agent**: TBD  
**Vertical Gap**: Single-entity command scope

## Problem

Current: Single-entity only
```python
entity Order {
  command Place {
    emit OrderPlaced  # Can't atomically reserve inventory
  }
}
```

Gap: Atomic cross-entity
```python
command PlaceOrder {
  atomic {
    Order.Create { ... }
    Inventory.Reserve { ... }
    Payment.Hold { ... }
  }
}
```

## Core IR

```typescript
export type WorkflowCommandSpecV0 = {
  type: "atomic"
  steps: Array<{
    entity_type: string
    command: string
    input_map: Record<string, ExprV0>
  }>
  compensation?: Array<...>  // Saga compensation
}
```

## Milestones

### BU1: Core IR Extension
- [x] BU1.1: WorkflowCommandSpecV0
- [x] BU1.2: Transaction boundary semantics
- [x] BU1.3: Partial failure handling
- [x] BU1.4: Update IR validator

### BU2: Multi-Entity Runtime
- [x] BU2.1: Saga orchestrator
- [x] BU2.2: Compensation on failure
- [x] BU2.3: Idempotency across streams
- [x] BU2.4: Conformance testing
