# Release v1.5.0 - Event-Driven Architecture Complete

**Theme**: Inbound webhooks for async message ingestion  
**Assigned Agent**: AGENT_GEMINI  
**Depends on**: v1.4.0 (WebSockets BL)

## Overview

v1.5.0 completes CICSC's event-driven architecture by adding **inbound webhooks** for reliable async message ingestion. External systems can now push events into CICSC with fire-and-forget semantics, queue buffering, and automatic retries.

## User Intent Addressed

> "When PagerDuty fires an alert, I want CICSC to create an incident ticket automatically—even if our system is temporarily overloaded. PagerDuty shouldn't need to retry or know about our downtime."

## Features

### 1. Declarative Inbound Webhooks (Spec DSL)
```
webhook PagerDutyAlert {
  payload { incident: { title, urgency, id } }
  verify_hmac { header: "X-PagerDuty-Signature", secret: env.PD_SECRET }
  idempotency_key: payload.incident.id
  map_to: command Incident.CreateIncident { ... }
}
```

### 2. Async Ingestion Server
- `POST /hook/:name` endpoint returns 202 Accepted immediately
- HMAC-SHA256 signature verification
- Idempotency key deduplication
- Queue-based buffering for resilience

### 3. Reliable Processing
- Exponential backoff retry (5 attempts)
- Dead letter queue for permanent failures
- Manual replay via admin API
- Per-source ordering guarantees

### 4. Security
- HMAC signature verification per webhook
- Timestamp replay protection (5-min window)
- Optional source IP allowlist
- Secret management via environment variables

## Architecture Completion

v1.5.0 completes the event-driven triangle:

```
        External Systems
              │
              ▼ webhook (BM)
        ┌─────────────┐
        │    CICSC    │◄──────┐
        │  (event     │       │
        │   store)    │───────┘
        └──────┬──────┘ websocket (BL)
               │
        ┌──────▼──────┐
        │   Browsers  │
        │  (live UI)  │
        └─────────────┘
               │
               ▼ webhook (BK - v1.6.0)
        External Notifications
```

## Checklist

- [x] BM1.1-1.4: Spec DSL extension for webhooks
- [x] BM2.1-2.4: Ingestion server with HMAC and idempotency
- [x] BM3.1-3.4: Async processing with retry and DLQ

## Migration from Sync to Async

Before (v1.4.0 and earlier):
```typescript
// PagerDuty must handle failures
try {
  await fetch('/cmd/Incident/CreateIncident', { method: 'POST', body })
} catch (e) {
  // Must retry or alert will be lost
}
```

After (v1.5.0):
```typescript
// PagerDuty fires and forgets
await fetch('/hook/PagerDutyAlert', { 
  method: 'POST', 
  body,
  headers: { 'X-PagerDuty-Signature': signature }
})
// 202 Accepted - CICSC handles the rest
```

## Test Coverage

| Test | Description |
|------|-------------|
| HMAC verification | Valid/invalid signatures rejected correctly |
| Idempotency | Duplicate webhooks processed once |
| Retry logic | Failed processing retried with backoff |
| Dead letter | Max retries → DLQ with replay capability |
| Load test | 10k webhooks/sec ingestion |
| Security | Replay attacks, signature forgery blocked |

## Future Work (v1.6.0+)

- **Outbound Webhooks (BK)**: CICSC → External notifications
- **CloudEvents**: Standardized event format
- **EventBridge**: AWS native integration
- **Transform DSL**: jq-like payload transformation
