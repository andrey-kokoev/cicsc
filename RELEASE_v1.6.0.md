# Release v1.6.0 - Queue Primitive

**Theme**: Reliable async processing with queue primitive  
**Assigned Agent**: AGENT_KIMI  
**Depends on**: v1.5.0 (Inbound Webhooks BM)

## Overview

v1.6.0 adds `queue` as a first-class Core IR primitive, enabling reliable async message processing with buffering, retries, dead letter queues, and observability.

## User Intent Addressed

> "When PagerDuty floods us with 1000 alerts during an outage, I want them queued and processed at our pace—not dropped. And when something breaks, I need to see what's stuck and replay it."

## Core IR Extension

```typescript
queue WebhookIngress {
  message_type { payload: json, headers: map, received_at: time }
  ordering: fifo
  retention { max_age_seconds: 86400, max_depth: 10000 }
  delivery { max_attempts: 5, dead_letter_queue: WebhookDLQ }
  map_to: command Incident.CreateIncident { ... }
}
```

## Features

### 1. Declarative Queues (Spec DSL)
- Typed message payloads
- FIFO/per-key/unordered ordering
- Configurable retention and backpressure
- Dead letter queue routing

### 2. Reliable Delivery
- Exponential backoff retry (1s, 2s, 4s, 8s, 16s)
- Max 5 attempts before DLQ
- Idempotency key deduplication (24h window)
- Visibility timeouts for safe concurrency

### 3. Webhook Integration
- Webhooks optionally route through queue: `queue: WebhookIngress`
- Returns `202 Accepted` instead of blocking
- Queue worker transforms and executes commands

### 4. Observability
```
GET /admin/queues              # Queue depth, oldest message age
GET /admin/queues/:name/dlq    # List dead letters
POST /admin/queues/:name/dlq/:id/replay  # Manual retry
DELETE /admin/queues/:name/dlq/:id       # Purge
```

## Architecture

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
              │ Worker   │          │ Retry    │          │ DLQ      │
              │ (success)│          │ (backoff)│          │ (manual  │
              │          │          │          │          │  replay) │
              └──────────┘          └──────────┘          └──────────┘
```

## Database Schema

```sql
CREATE TABLE queue_webhook_ingress (
  id TEXT PRIMARY KEY,
  message_json TEXT NOT NULL,
  idempotency_key TEXT UNIQUE,
  attempts INTEGER DEFAULT 0,
  visible_after INTEGER,  -- Visibility timeout
  created_at INTEGER NOT NULL
);
```

## Checklist

- [x] BN1.1-1.4: Core IR queue extension
- [x] BN2.1-2.4: Queue runtime (storage, worker, DLQ)
- [x] BN3.1-3.4: Webhook integration and observability

## Migration from Sync Webhooks

Before (v1.5.0):
```
webhook PagerDutyAlert {
  verify_hmac { ... }
  // Immediate execution
}
```

After (v1.6.0):
```
queue WebhookIngress {
  message_type { ... }
  delivery { max_attempts: 5 }
  map_to: command Incident.CreateIncident { ... }
}

webhook PagerDutyAlert {
  queue: WebhookIngress  // Buffered, reliable
  verify_hmac { ... }
}
```

## Test Coverage

| Test | Description |
|------|-------------|
| Enqueue | Webhook → queue table within 100ms |
| Retry | Failed message retried with backoff |
| DLQ | Max attempts → dead letter queue |
| Idempotency | Duplicate key returns cached result |
| Backpressure | Max depth → 503 rejection |
| Replay | DLQ message replayed successfully |

## Future Work (v1.7.0+)

- **Outbound Webhooks (BK)**: Use queue for reliable external delivery
- **Queue chaining**: Queue A → process → Queue B
- **Scheduled messages**: Delayed enqueue
- **SQS adapter**: Native AWS SQS backend
