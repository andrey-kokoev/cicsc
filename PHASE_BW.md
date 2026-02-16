# Phase BW: Service Primitive - External System Integration

**Status**: PLANNED  
**Agent**: AGENT_GEMINI  
**Goal**: Add `service` as first-class primitive for outgoing external integrations with sync and async (return address) semantics

## Problem Statement

Current CICSC can receive webhooks but cannot **call out** to external systems in a structured way:

| Direction | Current | Gap |
|-----------|---------|-----|
| **Incoming** | `webhook` primitive | ✅ |
| **Outgoing sync** | Ad-hoc fetch in commands | No typing, retry, circuit breaker |
| **Outgoing async** | Not supported | No return address pattern |

Sarah needs:
- "Charge customer's card via Stripe" (sync)
- "Send email via SendGrid, handle bounce later" (async)
- "Call internal microservice, retry if down" (reliability)

## Core IR Extension

```typescript
export type CoreIrV0 = {
  // ... existing
  services?: Record<string, ServiceSpecV0>
}

export type ServiceSpecV0 = {
  type: "http" | "graphql" | "grpc"
  base_url?: string                    // For HTTP services
  auth?: ServiceAuthV0                 // API keys, OAuth, etc.
  
  operations: Record<string, ServiceOperationV0>
  
  // Service-wide defaults
  timeout_seconds?: number
  retry?: RetryPolicyV0
  circuit_breaker?: CircuitBreakerConfigV0
}

export type ServiceAuthV0 =
  | { bearer_token_env: string }
  | { api_key_header: { header: string; key_env: string } }
  | { oauth2: { client_id_env: string; client_secret_env: string; token_url: string } }

export type ServiceOperationV0 = {
  method?: "GET" | "POST" | "PUT" | "DELETE"  // For HTTP
  path?: string                               // URL path template
  input: Record<string, AttrTypeSpecV0>       // Request payload schema
  output?: Record<string, AttrTypeSpecV0>     // Response schema (sync only)
  error?: Record<string, AttrTypeSpecV0>      // Error schema
  
  // Execution mode
  async?: boolean                             // Default: false (sync)
  return_address?: {                         // For async operations
    webhook: string                           // Webhook name to receive result
    correlation_id_field: string              // Field in input for correlation
    timeout: string                           // ISO duration, e.g., "5m"
  }
  
  // Overrides for service defaults
  timeout_seconds?: number
  retry?: RetryPolicyV0
}

export type RetryPolicyV0 = {
  max_attempts: number
  backoff: "fixed" | "exponential"
  initial_delay_ms: number
  max_delay_ms?: number
}

export type CircuitBreakerConfigV0 = {
  failure_threshold: number       // Failures to open circuit
  recovery_timeout_seconds: number
  half_open_max_calls: number
}

// New command emit type: service call
export type CommandEmitV0 = 
  | { event_type: string; payload: Record<string, ExprV0> }  // Existing
  | { call: ServiceCallV0 }                                   // NEW

export type ServiceCallV0 = {
  service: string
  operation: string
  input: Record<string, ExprV0>
  
  // Sync only: handle response inline
  on_success?: { emit: Array<CommandEmitV0> }
  on_error?: { emit: Array<CommandEmitV0> }
  
  // Async: result comes via return_address webhook
}
```

## Spec DSL Example

```python
service StripeAPI {
  type: http
  base_url: "https://api.stripe.com/v1"
  auth: { bearer_token_env: "STRIPE_API_KEY" }
  
  timeout: "30s"
  retry: { max_attempts: 3, backoff: exponential, initial_delay_ms: 1000 }
  
  operation CreateCharge {
    method: POST
    path: "/charges"
    input: { amount: int, currency: string, source: string }
    output: { id: string, status: string, receipt_url: string }
    error: { code: string, message: string, decline_code: string }
  }
  
  operation RefundCharge {
    method: POST
    path: "/refunds"
    input: { charge_id: string, amount: int }
    async: true
    return_address: {
      webhook: StripeRefundProcessed
      correlation_id_field: "refund_request_id"
      timeout: "5m"
    }
  }
}

service SendGrid {
  type: http
  base_url: "https://api.sendgrid.com/v3"
  auth: { api_key_header: { header: "Authorization", key_env: "SENDGRID_API_KEY" } }
  
  operation SendEmail {
    method: POST
    path: "/mail/send"
    input: { to: string, subject: string, body: string }
    async: true
    return_address: {
      webhook: EmailDelivered
      correlation_id_field: "message_id"
      timeout: "1h"
    }
  }
}

# Webhook that receives async results
webhook StripeRefundProcessed {
  verify_hmac { header: "Stripe-Signature", secret_env: "STRIPE_WEBHOOK_SECRET" }
  map_to: command CompleteRefund {
    refund_request_id: payload.correlation_id
    stripe_refund_id: payload.data.id
    status: payload.data.status
  }
}

webhook EmailDelivered {
  map_to: command MarkEmailDelivered {
    message_id: payload.correlation_id
    delivered_at: payload.timestamp
    bounce_reason: payload.bounce_reason
  }
}

# Usage in commands
entity Order {
  attr total: float
  attr status: "pending" | "paid" | "refunded"
  
  command PlaceOrder {
    input { payment_method: string }
    guard: true
    
    # Sync call - blocks for response
    call service StripeAPI.CreateCharge {
      input: {
        amount: order.total * 100,  # Convert to cents
        currency: "usd",
        source: input.payment_method
      }
      on_success: {
        emit PaymentCharged { charge_id: call.output.id }
        emit OrderPlaced
      }
      on_error: {
        emit PaymentFailed { 
          reason: call.error.message,
          code: call.error.decline_code 
        }
      }
    }
  }
  
  command RequestRefund {
    guard: order.status == "paid"
    
    # Async call - returns immediately, result via webhook
    call service StripeAPI.RefundCharge {
      input: {
        charge_id: order.charge_id,
        amount: order.total * 100,
        refund_request_id: new_uuid()  # Correlation ID
      }
    }
    
    emit RefundRequested { request_id: input.refund_request_id }
  }
  
  command CompleteRefund {
    input { refund_request_id: string, stripe_refund_id: string, status: string }
    guard: true
    
    emit RefundCompleted { 
      request_id: input.refund_request_id,
      stripe_id: input.stripe_refund_id,
      status: input.status
    }
    emit OrderRefunded
  }
}
```

## Database Schema

```sql
-- Pending async service calls
CREATE TABLE pending_service_calls (
  id TEXT PRIMARY KEY,              -- Correlation ID
  tenant_id TEXT NOT NULL,
  
  service_name TEXT NOT NULL,
  operation_name TEXT NOT NULL,
  
  -- Request details
  request_payload TEXT NOT NULL,
  return_address_url TEXT NOT NULL,  -- Unique webhook URL
  
  -- Timing
  created_at INTEGER NOT NULL,
  timeout_at INTEGER NOT NULL,
  
  -- Status
  status: "pending" | "completed" | "timeout" | "failed"
  
  -- Result (filled when webhook received)
  response_payload TEXT,
  completed_at INTEGER,
  
  -- For cleanup
  retry_count INTEGER DEFAULT 0,
  last_retry_at INTEGER
);

-- Index for cleanup job
CREATE INDEX idx_pending_calls_timeout 
  ON pending_service_calls(timeout_at) 
  WHERE status = 'pending';

-- Index for lookup by return address
CREATE INDEX idx_pending_calls_url 
  ON pending_service_calls(return_address_url);
```

## Return Address Mechanism

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         SYNC CALL FLOW                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Command → call service.Operation { input }                             │
│                    │                                                     │
│                    ▼                                                     │
│            ┌───────────────┐                                             │
│            │ HTTP Client   │                                             │
│            │ - Add auth    │                                             │
│            │ - Retry logic │                                             │
│            │ - Timeout     │                                             │
│            └───────┬───────┘                                             │
│                    │                                                     │
│                    ▼                                                     │
│            External Service                                              │
│                    │                                                     │
│                    ▼                                                     │
│            ┌───────────────┐                                             │
│            │ Parse response│                                             │
│            │ Match output  │                                             │
│            │ or error      │                                             │
│            └───────┬───────┘                                             │
│                    │                                                     │
│         ┌─────────┴─────────┐                                            │
│         ▼                   ▼                                            │
│    on_success            on_error                                        │
│    (emit events)         (emit events)                                   │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────────────┐
│                        ASYNC CALL FLOW                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│   Command → call service.Operation {                                     │
│               input: { ..., correlation_id: uuid() }                     │
│             }                                                            │
│                    │                                                     │
│                    ▼                                                     │
│            ┌───────────────┐                                             │
│            │ Store pending │                                             │
│            │ call record   │                                             │
│            │ with timeout  │                                             │
│            └───────┬───────┘                                             │
│                    │                                                     │
│                    ▼                                                     │
│            ┌───────────────┐                                             │
│            │ HTTP POST     │                                             │
│            │ + return_url  │  https://api.cicsc.dev/webhook/return/abc123
│            └───────┬───────┘                                             │
│                    │                                                     │
│                    ▼                                                     │
│            External Service                                              │
│                    │                                                     │
│         (async processing...)                                            │
│                    │                                                     │
│                    ▼                                                     │
│            POST to return_url                                            │
│                    │                                                     │
│                    ▼                                                     │
│            Webhook receives result                                       │
│                    │                                                     │
│                    ▼                                                     │
│            ┌───────────────┐                                             │
│            │ Lookup pending│                                             │
│            │ call by URL   │                                             │
│            └───────┬───────┘                                             │
│                    │                                                     │
│                    ▼                                                     │
│            Execute mapped command                                        │
│            (e.g., CompleteRefund)                                        │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

## Integration with Existing Primitives

| Primitive | How Service Uses It |
|-----------|-------------------|
| **Queue (BN)** | Async calls queued for reliability |
| **Schedule (BO)** | Timeout handling, retry scheduling |
| **Webhook (BM)** | Return address receives results |
| **Workflow (BP)** | Service calls as workflow steps |
| **Saga (BU)** | Compensation for failed service calls |

## Milestones

### BW1: Core IR Service Extension
- [x] BW1.1: Add ServiceSpecV0 to Core IR
- [x] BW1.2: Define sync operation semantics
- [x] BW1.3: Define async operation with return_address
- [x] BW1.4: Add call expression to command emit

### BW2: Return Address and Correlation
- [x] BW2.1: Return address URL generation
- [x] BW2.2: Correlation ID tracking
- [x] BW2.3: Webhook-to-command mapping
- [x] BW2.4: Timeout and cleanup

### BW3: Service Runtime and Reliability
- [x] BW3.1: HTTP client abstraction
- [x] BW3.2: Retry policy with backoff
- [x] BW3.3: Circuit breaker
- [x] BW3.4: Queue integration

### BW4: Integration and Testing
- [x] BW4.1: Service mocking
- [x] BW4.2: Observability
- [x] BW4.3: Dead call detection
- [x] BW4.4: Documentation and examples
