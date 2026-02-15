# Phase BT: Row-Level Security Sugar

**Status**: PLANNED (v1.9.0)  
**Agent**: TBD  
**Vertical Gap**: No Spec-level RLS patterns

## Problem

Current: Runtime-only, verbose
```python
view MyTickets {
  query: Ticket
  # Runtime row_policy only
}
```

Gap: Spec-level sugar
```python
view MyTickets {
  query: Ticket
  row_policy: owner  # Sugar: where owner_id == actor.id
}

view TeamTickets {
  query: Ticket
  row_policy: member_of(team)  # Team membership
}
```

## Core IR

```typescript
export type ViewSpecV0 = {
  // ... existing
  row_policy?: 
    | { expr: ExprV0 }           // Custom (existing)
    | { owner: { field: string } }  // NEW: owner pattern
    | { member_of: { entity: string; field: string } }  // NEW
}
```

## Milestones

### BT1: Core IR Extension
- [x] BT1.1: Add row_policy patterns
- [x] BT1.2: Define owner semantics
- [x] BT1.3: Define member_of semantics
- [x] BT1.4: Update IR validator

### BT2: RLS Runtime
- [x] BT2.1: Owner pattern codegen
- [x] BT2.2: Member-of pattern codegen
- [x] BT2.3: Fallback to custom expr
- [x] BT2.4: RLS enforcement
