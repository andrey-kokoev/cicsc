# Release v1.8.0 - Workflow Primitive

**Theme**: Multi-entity orchestration with Saga pattern  
**Assigned Agent**: AGENT_GEMINI  
**Depends on**: v1.6.0 (Queue BN)

## Overview

v1.8.0 adds workflow as Core IR primitive for distributed transactions across multiple entities with automatic compensation (Saga pattern).

## User Intent

> "When a customer places an order, I need to reserve inventory, charge their card, and create a shipment—all or nothing. If payment fails, release the inventory automatically."

## Core IR Extension

```typescript
workflow OrderFulfillment {
  input { customer_id, items, address }
  execution { timeout: "1h", queue: ReliableQueue }
  
  steps: [
    { name: "create_order", type: command, command: Order.Create { ... } }
    { name: "reserve_inventory", type: command, command: Inventory.Reserve { ... } }
    { name: "charge_payment", type: command, command: Payment.Charge { ... }, on_failure: compensate }
    { name: "create_shipment", type: command, command: Shipment.Create { ... } }
  ]
  
  compensation: [
    { for_step: "reserve_inventory", action: Inventory.Release { ... } }
    { for_step: "charge_payment", action: Payment.Refund { ... } }
  ]
}
```

## Features

### Step Types
- **command**: Invoke entity command
- **wait**: Pause for event with timeout
- **decide**: Conditional routing

### Saga Compensation
- Automatic rollback on failure
- Reverse order execution
- Conditional compensation (only undo what succeeded)

### Integration
- Route through queue for reliability
- Event-driven step advancement
- Real-time status via WebSocket

## API

```
POST /workflow/:name/start
GET  /workflow/:id           # Status and step history
POST /workflow/:id/cancel    # Trigger compensation
GET  /workflows              # List with filters
```

## Comparison

| Aspect | Entity State Machine | Workflow |
|--------|---------------------|----------|
| Scope | Single entity | Multiple entities |
| Transaction | Atomic | Distributed (Saga) |
| Failure | Rollback command | Compensating transactions |

## Checklist

- [x] BP1.1-1.4: Core IR workflow extension
- [x] BP2.1-2.4: Workflow runtime engine
- [x] BP3.1-3.4: API and observability

## Gemini's Complete Stack

```
v1.4.0  BL  WebSocket  → Real-time
v1.5.0  BM  Webhook    → Ingest
v1.6.0  BN  Queue      → Reliable execution
v1.7.0  BO  Schedule   → Time-based
v1.8.0  BP  Workflow   → Orchestration
```
