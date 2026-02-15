# Phase BP: Workflow Primitive - Multi-Entity Orchestration

**Status**: PLANNED (v1.8.0)  
**Agent**: AGENT_GEMINI  
**Goal**: Add workflow as Core IR primitive for distributed transactions with Saga pattern

## Problem Statement

Current CICSC handles single-entity state machines well:

```
Ticket: Open → InProgress → Resolved
```

But real business processes span multiple entities with distributed transactions:

```
Order Fulfillment:
  1. Create Order
  2. Reserve Inventory (separate entity)
  3. Charge Payment (separate entity)  
  4. Ship Order (separate entity)
  5. Send Confirmation

Problem: Step 3 fails → Need to undo steps 1-2
         (release inventory, cancel order)
```

Without workflow primitive:
- Ad-hoc orchestration code in commands
- No visibility into process state
- Compensation logic scattered
- No recovery from partial failures

## User Intent

**Maria** (e-commerce platform lead):
> "When a customer places an order, I need to reserve inventory, charge their card, and create a shipment—all or nothing. If payment fails, release the inventory automatically. I want to see exactly where each order is in this flow."

## Core IR Extension

```typescript
// core/ir/types.ts additions
export type CoreIrV0 = {
  // ... existing: types, queues, schedules, etc.
  workflows?: Record<string, WorkflowSpecV0>
}

export type WorkflowSpecV0 = {
  input: Record<string, AttrTypeSpecV0>
  steps: WorkflowStepV0[]
  compensation?: CompensationSpecV0[]
  execution: {
    timeout_seconds?: number
    max_retries_per_step?: number
    queue?: string
  }
}

export type WorkflowStepV0 = {
  name: string
  type: "command" | "wait" | "decide"
  command?: {
    entity_type: string
    command: string
    input_map: Record<string, ExprV0>
    entity_id?: ExprV0
  }
  wait?: {
    for_event: string
    on_entity?: ExprV0
    timeout_seconds?: number
    on_timeout?: "fail" | "continue" | "compensate"
  }
  decide?: {
    condition: ExprV0
    then: string
    else: string
  }
  next?: string
  on_failure?: "retry" | "fail" | "compensate"
}

export type CompensationSpecV0 = {
  for_step: string
  action: {
    entity_type: string
    command: string
    input_map: Record<string, ExprV0>
    entity_id: ExprV0
  }
  condition?: ExprV0
}
```

## Spec DSL Example

```
app EcommercePlatform {
  entity Order { ... }
  entity Inventory { ... }
  entity Payment { ... }
  entity Shipment { ... }
  
  workflow OrderFulfillment {
    input {
      customer_id: string
      items: list<{ sku: string, quantity: int }>
      address: string
      payment_method: string
    }
    
    execution {
      timeout: "1h"
      max_retries_per_step: 3
      queue: ReliableQueue
    }
    
    steps: [
      {
        name: "create_order"
        type: command
        command: Order.Create {
          input_map: { customer_id: workflow.input.customer_id }
        }
      }
      {
        name: "reserve_inventory"
        type: command
        command: Inventory.Reserve { ... }
      }
      {
        name: "charge_payment"
        type: command
        command: Payment.Charge { ... }
        on_failure: compensate
      }
      {
        name: "create_shipment"
        type: command
        command: Shipment.Create { ... }
      }
      {
        name: "wait_shipped"
        type: wait
        wait: {
          for_event: "ShipmentShipped"
          timeout: "7d"
          on_timeout: compensate
        }
      }
    ]
    
    compensation: [
      {
        for_step: "reserve_inventory"
        action: Inventory.Release { ... }
      }
      {
        for_step: "charge_payment"
        action: Payment.Refund { ... }
      }
      {
        for_step: "create_order"
        action: Order.Cancel { ... }
      }
    ]
  }
}
```

## Database Schema

```sql
CREATE TABLE workflow_instances (
  id TEXT PRIMARY KEY,
  workflow_name TEXT NOT NULL,
  tenant_id TEXT NOT NULL,
  input_json TEXT NOT NULL,
  status TEXT DEFAULT 'pending',
  current_step TEXT,
  started_at INTEGER,
  completed_at INTEGER,
  timeout_at INTEGER,
  result_json TEXT,
  error TEXT,
  saga_log TEXT
);

CREATE TABLE workflow_steps (
  id TEXT PRIMARY KEY,
  workflow_id TEXT NOT NULL,
  step_name TEXT NOT NULL,
  status TEXT,
  started_at INTEGER,
  completed_at INTEGER,
  entity_type TEXT,
  entity_id TEXT,
  command_name TEXT,
  input_json TEXT,
  result_json TEXT,
  error TEXT,
  compensated_at INTEGER,
  compensation_error TEXT
);
```

## API

```typescript
// Start workflow
POST /workflow/:name/start
{ "input": { ... } }
// Response: { "workflow_id": "wf_abc123", "status": "pending" }

// Get status
GET /workflow/:workflow_id
{
  "id": "wf_abc123",
  "status": "running",
  "current_step": "charge_payment",
  "steps": [...]
}

// Cancel (triggers compensation)
POST /workflow/:workflow_id/cancel
```

## Milestones

### BP1: Core IR Workflow Extension
- [x] BP1.1: Add WorkflowSpecV0 to Core IR
- [x] BP1.2: Define step types (command, wait, decision)
- [x] BP1.3: Define compensation semantics (Saga pattern)
- [x] BP1.4: Update IR validator

### BP2: Workflow Runtime
- [x] BP2.1: Workflow state machine
- [x] BP2.2: Step executor
- [x] BP2.3: Compensation engine
- [x] BP2.4: Workflow persistence

### BP3: Integration
- [x] BP3.1: Workflow initiation API
- [x] BP3.2: Event-driven step triggering
- [x] BP3.3: Workflow admin API
- [x] BP3.4: Dead workflow recovery

## Gemini's Platform Stack

```
v1.4.0  BL  WebSocket  → Real-time updates
v1.5.0  BM  Webhook    → External events  
v1.6.0  BN  Queue      → Reliable execution
v1.7.0  BO  Schedule   → Time-based execution
v1.8.0  BP  Workflow   → Multi-entity orchestration
```
