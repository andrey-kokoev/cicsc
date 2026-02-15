# Phase BM: Inbound Webhooks - Async Message Ingestion

**Status**: PLANNED (v1.5.0)  
**Agent**: AGENT_GEMINI  
**Goal**: Enable external systems to push events into CICSC asynchronously with reliability guarantees

## User Intent Scenario

**Sarah** (incident response lead):
> "When PagerDuty fires an alert, I want CICSC to create an incident ticket automatically—even if our system is temporarily overloaded. PagerDuty shouldn't need to retry or know about our downtime."

**Current State**: External systems must POST to `/cmd` and wait for synchronous response. If CICSC is down or slow, the external caller fails and may drop the event.  
**Desired State**: Fire-and-forget ingestion with queue buffering, retries, and idempotency.

## Acceptance Criteria

1. Declare in Spec: `webhook PagerDutyAlert: { ...schema... } → command CreateIncident`
2. PagerDuty POSTs to `POST /hook/PagerDutyAlert` with HMAC signature
3. CICSC returns 202 Accepted immediately, queues for processing
4. Failed deliveries retried with exponential backoff
5. Dead letter queue after max retries; manual replay available
6. Duplicate webhooks (same idempotency key) processed exactly once

## Spec DSL Design

```
app IncidentManagement {
  entity Incident {
    attr title: string
    attr severity: "critical" | "high" | "medium" | "low"
    attr source: string
    attr external_id: string
    
    command CreateIncident {
      input { title, severity, source, external_id }
      guard: true
      emit IncidentCreated
    }
  }
  
  // Inbound webhook declaration
  webhook PagerDutyAlert {
    // Payload schema from external system
    payload {
      incident: {
        title: string
        urgency: "high" | "low"  // mapped to severity
        html_url: string
        id: string               // becomes external_id
      }
    }
    
    // Security: verify HMAC signature
    verify_hmac {
      header: "X-PagerDuty-Signature"
      secret: env.PAGERDUTY_WEBHOOK_SECRET
    }
    
    // Idempotency key extraction
    idempotency_key: payload.incident.id
    
    // Transform payload to command input
    map_to: command Incident.CreateIncident {
      title: payload.incident.title
      severity: payload.incident.urgency == "high" ? "critical" : "high"
      source: "pagerduty"
      external_id: payload.incident.id
    }
  }
  
  webhook GitHubIssue {
    payload { action, issue: { title, number, html_url } }
    verify_hmac { header: "X-Hub-Signature-256", secret: env.GITHUB_WEBHOOK_SECRET }
    idempotency_key: payload.issue.number
    filter: payload.action == "opened"
    map_to: command Incident.CreateIncident {
      title: "[GitHub] " + payload.issue.title
      severity: "medium"
      source: "github"
      external_id: string(payload.issue.number)
    }
  }
}
```

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         EXTERNAL SYSTEMS                                │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐                │
│  │PagerDuty │  │  GitHub  │  │  Stripe  │  │  Custom  │                │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────┬─────┘                │
└───────┼─────────────┼─────────────┼─────────────┼──────────────────────┘
        │             │             │             │
        │ POST /hook  │             │             │
        │ + HMAC      │             │             │
        ▼             ▼             ▼             ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                      WEBHOOK INGESTION LAYER                            │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │  POST /hook/:name                                               │   │
│  │  ├── 1. HMAC verification (reject 401 if invalid)               │   │
│  │  ├── 2. Idempotency check (return 200 if already processed)     │   │
│  │  ├── 3. Payload validation (return 400 if schema mismatch)      │   │
│  │  └── 4. Queue for async processing (return 202 Accepted)        │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                              │                                          │
│                              ▼                                          │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │  QUEUE (D1/Redis/SQS)                                           │   │
│  │  ├── Buffer during high load                                    │   │
│  │  ├── Persist for durability                                     │   │
│  │  └── Ordered delivery per source                                │   │
│  └─────────────────────────────────────────────────────────────────┘   │
└──────────────────────────────┬──────────────────────────────────────────┘
                               │
                               ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    ASYNC PROCESSING WORKER                              │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │  FOR EACH MESSAGE:                                              │   │
│  │  ├── Deserialize payload                                        │   │
│  │  ├── Transform (webhook payload → command input)                │   │
│  │  ├── Execute command (same path as sync /cmd)                   │   │
│  │  ├── Record success (idempotency store)                         │   │
│  │  └── On failure: retry with backoff → dead letter queue         │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│                              │                                          │
│                    ┌─────────┴──────────┐                               │
│                    ▼                    ▼                               │
│            ┌──────────────┐    ┌─────────────────┐                     │
│            │  EVENT STORE │    │  DEAD LETTER    │                     │
│            │  (entities)  │    │  QUEUE (DLQ)    │                     │
│            └──────────────┘    │  - max retries  │                     │
│                                │  - manual replay│                     │
│                                └─────────────────┘                     │
└─────────────────────────────────────────────────────────────────────────┘
```

## Message Flow

```typescript
// 1. External system sends webhook
POST /hook/PagerDutyAlert
Headers:
  X-PagerDuty-Signature: v1=abc123def456...
  Content-Type: application/json
Body:
  { "incident": { "title": "DB down", "urgency": "high", "id": "PD-123" } }

// 2. Ingestion server response (immediate)
202 Accepted
{ "ok": true, "queued": true, "idempotency_key": "PD-123" }

// 3. Queue entry
{
  "id": "msg_abc123",
  "webhook_name": "PagerDutyAlert",
  "idempotency_key": "PD-123",
  "payload": { ... },
  "received_at": 1708000000,
  "attempts": 0,
  "status": "pending"
}

// 4. Processing (async)
// - Transform payload to CreateIncident input
// - Execute command
// - Store idempotency record

// 5. On max retries exceeded → Dead Letter Queue
{
  "id": "msg_abc123",
  "error": "Command failed: guard rejected",
  "failed_at": 1708003600,
  "retryable": false
}
```

## Security Model

| Layer | Mechanism | Config |
|-------|-----------|--------|
| **Authentication** | HMAC-SHA256 signature | `verify_hmac { header, secret }` in Spec |
| **Idempotency** | Key-based deduplication | `idempotency_key: <expr>` in Spec |
| **Authorization** | Source IP allowlist | `allow_ips: ["52.x.x.x/24"]` (optional) |
| **Replay protection** | Timestamp window | Reject if timestamp > 5 min old |

## Retry Policy

```
Attempt 1: Immediate
Attempt 2: After 5 seconds
Attempt 3: After 25 seconds  
Attempt 4: After 2 minutes
Attempt 5: After 10 minutes

Max attempts: 5
Dead letter after: 5 failures
Manual replay: Admin API endpoint
```

## Comparison: Sync vs Async Ingestion

| Aspect | Sync REST (`/cmd`) | Async Webhook (`/hook`) |
|--------|-------------------|-------------------------|
| **Coupling** | Tight (caller waits) | Loose (fire-and-forget) |
| **Resilience** | Caller must handle failures | Queue absorbs downtime |
| **Latency** | Full processing time | Immediate 202 response |
| **Throughput** | Limited by processing speed | Buffer absorbs bursts |
| **Ordering** | Guaranteed (serial) | Per-source ordering (configurable) |
| **Idempotency** | Manual (caller provides key) | Built-in (spec-defined key) |
| **Use case** | User interactions | External system events |

## Milestones

### BM1: Spec DSL Extension for Inbound Webhooks
- [x] **BM1.1**: Add 'webhook' keyword to Spec DSL for external event sources
- [x] **BM1.2**: Define webhook payload schema and validation
- [x] **BM1.3**: Map webhook payloads to commands (webhook → command binding)
- [x] **BM1.4**: Parse webhooks to Core IR with source metadata

### BM2: Webhook Ingestion Server
- [x] **BM2.1**: HTTP endpoint for webhook reception (`POST /hook/:name`)
- [x] **BM2.2**: HMAC signature verification middleware
- [x] **BM2.3**: Idempotency key handling (prevent duplicate processing)
- [x] **BM2.4**: Queue-based ingestion (buffer before processing)

### BM3: Async Processing & Delivery
- [x] **BM3.1**: Webhook-to-command transformation engine
- [x] **BM3.2**: Retry policy with exponential backoff
- [x] **BM3.3**: Dead letter queue for failed webhooks
- [x] **BM3.4**: Webhook delivery status tracking and replay

## Test Plan

1. **Unit**: HMAC verification with known-good/bad signatures
2. **Integration**: Full flow - webhook POST → queue → command execution
3. **Idempotency**: Same payload twice → one command execution
4. **Resilience**: Kill worker mid-processing → retry succeeds
5. **Load**: 10k webhooks/sec ingestion, measure queue depth
6. **Security**: Replay attack (old timestamp), invalid signature

## Relation to Other Phases

| Phase | Direction | Purpose |
|-------|-----------|---------|
| **BL** (WebSockets) | Bidirectional | Real-time client updates |
| **BK** (Outbound Webhooks) | CICSC → External | Notify external systems |
| **BM** (Inbound Webhooks) | External → CICSC | Receive external events (this phase) |

Together: **Complete event-driven architecture**

```
External ──webhook──► CICSC ──websocket──► Browser
      ▲                                    │
      └──────────webhook (BK)──────────────┘
```

## Future Enhancements

- **CloudEvents**: Standardize on CloudEvents spec for interoperability
- **EventBridge**: Native AWS EventBridge integration
- **Schema Registry**: Versioned webhook schemas with evolution
- **Transform DSL**: Richer payload transformation language (jq-like)
