# Phase BN: Queue Primitive - Reliable Async Processing

**Status**: PLANNED (v1.6.0)  
**Agent**: AGENT_GEMINI  
**Goal**: Add `queue` as a first-class Core IR primitive for reliable async message processing

## Problem Statement

Current webhook implementation (BM) processes requests **synchronously**:

```
PagerDuty ──POST /hook──► CICSC ──► executeCommand() ──► 200/500
                                (blocks, no retry)
```

This creates operational risks:
- **No buffering**: Burst traffic overwhelms the system
- **No retry**: Transient failures lose data
- **No visibility**: Can't see pending work or diagnose issues
- **Tight coupling**: External callers must handle our downtime

## User Intent

**Sarah** (platform engineer):
> "When PagerDuty floods us with 1000 alerts during an outage, I want them queued and processed at our pace—not dropped. And when something breaks, I need to see what's stuck and replay it."

## Solution: Queue as Core IR Primitive

```
PagerDuty ──POST /hook──► CICSC ──► 202 Accepted
                                          │
                                          ▼
                                    ┌────────────┐
                                    │   QUEUE    │ (buffered, persistent)
                                    └─────┬──────┘
                                          │
                    ┌─────────────────────┼─────────────────────┐
                    │                     │                     │
                    ▼                     ▼                     ▼
              ┌──────────┐          ┌──────────┐          ┌──────────┐
              │ Worker 1 │          │ Worker 2 │          │   DLQ    │
              │ (success)│          │ (retry)  │          │ (permanent failure)
              └──────────┘          └──────────┘          └──────────┘
```

## Core IR Extension

### Types

```typescript
// core/ir/types.ts additions
export type CoreIrV0 = {
  // ... existing fields
  queues?: Record<string, QueueSpecV0>
}

export type QueueSpecV0 = {
  // Typed message payload (like command input)
  message_type: Record<string, AttrTypeSpecV0>
  
  // Ordering semantics
  ordering?: "unordered" | "fifo" | "per_key"
  
  // Retention and backpressure
  retention: {
    max_age_seconds: number
    max_depth?: number  // Backpressure threshold
  }
  
  // Delivery guarantees
  delivery: {
    max_attempts: number
    initial_backoff_ms: number
    max_backoff_ms: number
    dead_letter_queue?: string  // References another queue
  }
  
  // Transform message to command (optional, for webhook integration)
  map_to?: QueueCommandMappingV0
}

export type QueueCommandMappingV0 = {
  entity_type: string
  command: string
  input_map: Record<string, ExprV0>  // expr over message fields
}

// Update WebhookSpecV0 to reference queue
export type WebhookSpecV0 = {
  on_type: string
  command: string
  queue?: string  // Process via queue instead of immediate
  verify?: { ... }
}
```

## Spec DSL Design

```
app IncidentManagement {
  // Queue definitions
  queue WebhookIngress {
    message_type {
      payload: json
      headers: map<string, string>
      source_ip: string
      received_at: time
    }
    
    ordering: fifo
    
    retention {
      max_age_seconds: 86400    // 24h TTL
      max_depth: 10000          // Reject new messages at 10k depth
    }
    
    delivery {
      max_attempts: 5
      initial_backoff_ms: 1000   // 1s, 2s, 4s, 8s, 16s
      max_backoff_ms: 60000      // Cap at 1 minute
      dead_letter_queue: WebhookDLQ
    }
    
    // Auto-transform to command
    map_to: command Incident.CreateIncident {
      title: payload.incident.title
      severity: payload.incident.urgency == "high" ? "critical" : "high"
      source: "pagerduty"
      external_id: payload.incident.id
    }
  }
  
  queue WebhookDLQ {
    message_type {
      original_message: json
      failed_at: time
      error: string
      attempts: int
    }
    retention { max_age_seconds: 604800 }  // 7 days for inspection
    // No map_to - manual replay only
  }
  
  // Webhook uses queue
  webhook PagerDutyAlert {
    queue: WebhookIngress  // <-- Routed through queue
    verify_hmac {
      header: "X-PagerDuty-Signature"
      secret_env: "PAGERDUTY_WEBHOOK_SECRET"
    }
  }
}
```

## Database Schema (SQLite/D1)

```sql
-- Main queue table (one per queue spec)
CREATE TABLE queue_webhook_ingress (
  id TEXT PRIMARY KEY,                    -- UUID
  message_json TEXT NOT NULL,             -- Serialized message
  idempotency_key TEXT UNIQUE,            -- Deduplication (24h window)
  
  -- Delivery state
  attempts INTEGER DEFAULT 0,
  visible_after INTEGER,                  -- Unix ms (visibility timeout)
  locked_by TEXT,                         -- Worker instance ID (optional)
  
  -- Timestamps
  created_at INTEGER NOT NULL,
  updated_at INTEGER NOT NULL,
  
  -- Indexing
  INDEX idx_visible (visible_after, created_at),  -- Poll query
  INDEX idx_idempotency (idempotency_key)         -- Deduplication
);

-- Dead letter queue
CREATE TABLE queue_webhook_dlq (
  id TEXT PRIMARY KEY,
  original_queue TEXT NOT NULL,           -- Source queue name
  message_json TEXT NOT NULL,
  failed_at INTEGER NOT NULL,
  error TEXT,
  attempts INTEGER,
  
  -- Replay support
  replayed_at INTEGER,
  replay_result TEXT
);

-- Idempotency tracking (separate table for TTL cleanup)
CREATE TABLE idempotency_keys (
  key TEXT PRIMARY KEY,
  queue_name TEXT NOT NULL,
  processed_at INTEGER NOT NULL,
  result_json TEXT                        -- Snapshot of success response
);

-- Cleanup job: DELETE FROM idempotency_keys WHERE processed_at < now - 24h
```

## Runtime Architecture

### Components

```
┌────────────────────────────────────────────────────────────────────────────┐
│                              HTTP WORKER                                    │
│  POST /hook/:name                                                          │
│  ├── HMAC verification (401 if invalid)                                    │
│ ├── Parse payload                                                          │
│  ├── Check idempotency (200 if already processed)                          │
│  ├── IF queue specified:                                                   │
│  │   └── Enqueue({ payload, headers, source_ip, received_at })             │
│  │   └── Return 202 Accepted { queued: true, idempotency_key }             │
│  └── ELSE (sync fallback):                                                 │
│      └── Execute command immediately                                       │
└────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌────────────────────────────────────────────────────────────────────────────┐
│                              QUEUE STORE                                    │
│  Interface:                                                                 │
│  - enqueue(message, idempotency_key?): Promise<void>                       │
│  - dequeue(queue_name): Promise<Message | null>                            │
│  - ack(message_id): Promise<void>                                          │
│  - retry(message_id, delay_ms): Promise<void>                              │
│  - dead_letter(message_id, error): Promise<void>                           │
└────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌────────────────────────────────────────────────────────────────────────────┐
│                              QUEUE WORKER                                   │
│  Background worker (Cloudflare Worker cron or Durable Object alarm)        │
│                                                                             │
│  FOR each queue with map_to:                                               │
│    WHILE true:                                                             │
│      msg = dequeue(queue_name)                                             │
│      IF msg is null: BREAK                                                 │
│                                                                             │
│      TRY:                                                                  │
│        input = transform(msg, queue.map_to.input_map)                      │
│        result = executeCommand(entity_type, command, input)                │
│        ack(msg.id)                                                         │
│        record_idempotency(msg.idempotency_key, result)                     │
│      CATCH error:                                                          │
│        IF msg.attempts >= max_attempts:                                    │
│          dead_letter(msg.id, error)                                        │
│        ELSE:                                                               │
│          retry(msg.id, backoff(msg.attempts))                              │
└────────────────────────────────────────────────────────────────────────────┘
```

### Queue Worker Pseudocode

```typescript
// runtime/queue/worker.ts
export class QueueWorker {
  constructor(
    private store: QueueStore,
    private ir: CoreIrV0,
    private commandExecutor: CommandExecutor
  ) {}

  async processQueue(queueName: string, batchSize: number = 10) {
    const queueSpec = this.ir.queues![queueName]
    
    for (let i = 0; i < batchSize; i++) {
      const msg = await this.store.dequeue(queueName)
      if (!msg) break

      try {
        // Transform message to command input
        const input = this.transformMessage(msg, queueSpec.map_to!.input_map)
        
        // Execute command
        await this.commandExecutor.execute({
          entity_type: queueSpec.map_to!.entity_type,
          command_name: queueSpec.map_to!.command,
          input,
          // ... other fields
        })

        await this.store.ack(msg.id)
      } catch (error) {
        if (msg.attempts >= queueSpec.delivery.max_attempts) {
          await this.store.deadLetter(queueName, msg.id, String(error))
        } else {
          const backoff = this.calculateBackoff(msg.attempts, queueSpec.delivery)
          await this.store.retry(msg.id, backoff)
        }
      }
    }
  }

  private calculateBackoff(attempts: number, delivery: DeliveryConfig): number {
    const delay = delivery.initial_backoff_ms * Math.pow(2, attempts)
    return Math.min(delay, delivery.max_backoff_ms)
  }
}
```

## Observability API

```typescript
// GET /admin/queues?tenant_id=...
{
  "queues": [{
    "name": "WebhookIngress",
    "depth": 42,                    // Messages waiting
    "in_flight": 3,                 // Messages being processed
    "oldest_message_age_seconds": 120,
    "messages_per_minute": 150
  }]
}

// GET /admin/queues/:name/dlq?tenant_id=...
{
  "dead_letters": [{
    "id": "msg_abc123",
    "failed_at": 1708000000,
    "error": "Command failed: guard rejected",
    "attempts": 5,
    "preview": { "payload": { "incident": { "title": "..." } } }
  }]
}

// POST /admin/queues/:name/dlq/:id/replay
{ "ok": true, "new_message_id": "msg_xyz789" }

// DELETE /admin/queues/:name/dlq/:id
{ "ok": true }  // Purge failed message
```

## Retry Backoff Visualization

```
Attempt 1: Immediate processing
     │
     ├──► FAIL ──► Wait 1s ──► Attempt 2
                              │
                              ├──► FAIL ──► Wait 2s ──► Attempt 3
                                                       │
                                                       ├──► FAIL ──► Wait 4s ──► Attempt 4
                                                                                │
                                                                                ├──► FAIL ──► Wait 8s ──► Attempt 5
                                                                                                         │
                                                                                                         ├──► FAIL ──► Dead Letter Queue
                                                                                                                           (manual replay or purge)
```

## Milestones

### BN1: Core IR Queue Extension
- [x] **BN1.1**: Add QueueSpecV0 to Core IR types (message_type, ordering, retention, delivery)
- [x] **BN1.2**: Add queue reference to WebhookSpecV0
- [x] **BN1.3**: Define queue message transformation expressions (map_to)
- [x] **BN1.4**: Update IR validator for queue specifications

### BN2: Queue Runtime Implementation
- [x] **BN2.1**: Queue storage abstraction (enqueue, dequeue, ack, retry)
- [x] **BN2.2**: SQLite/D1 queue table schema with visibility timeouts
- [x] **BN2.3**: Queue worker polling with backoff
- [x] **BN2.4**: Dead letter queue implementation

### BN3: Webhook Integration & Observability
- [x] **BN3.1**: Route webhooks through queue (202 Accepted → enqueue)
- [x] **BN3.2**: Idempotency tracking (24h window)
- [x] **BN3.3**: Queue metrics API (depth, oldest message, DLQ size)
- [x] **BN3.4**: DLQ admin API (list, inspect, replay)

## Acceptance Criteria

1. Webhook with `queue` specified returns 202 Accepted, not 200
2. Message visible in queue within 100ms of receipt
3. Failed messages retried 5 times with exponential backoff
4. After max retries, message appears in DLQ with error details
5. Idempotency key prevents duplicate processing for 24h
6. Queue depth metrics available via admin API
7. DLQ messages can be replayed via admin API
8. Load test: 10k webhooks enqueued and processed correctly

## Test Plan

| Test | Description |
|------|-------------|
| **Enqueue** | Webhook POST → message in queue table |
| **Dequeue** | Worker polls, receives visible message |
| **Visibility timeout** | Message not visible to other workers for N seconds |
| **Retry** | Failed processing increments attempts, sets visible_after |
| **DLQ** | Max attempts exceeded → moved to DLQ table |
| **Idempotency** | Same idempotency key twice → second returns cached result |
| **Ordering** | FIFO queue preserves message order per source |
| **Backpressure** | Queue at max_depth → new webhooks rejected 503 |
| **Replay** | DLQ message replayed → new queue entry, processed |

## Relation to Other Phases

| Phase | Feature | With BN Enhancement |
|-------|---------|---------------------|
| **BM** | Inbound Webhooks | + Queue buffering, retry, DLQ |
| **BK** | Outbound Webhooks | Can reuse queue for reliable delivery |
| **BL** | WebSockets | Queue can buffer broadcasts during high load |

## Future Extensions

- **Queue chaining**: Queue A → process → enqueue to Queue B
- **Scheduled messages**: `enqueue_at` for delayed processing
- **Priority queues**: Multiple priority levels within one queue
- **SQS adapter**: Native AWS SQS backend instead of SQLite
- **Event sourcing**: Queue as event log (persist all messages)
