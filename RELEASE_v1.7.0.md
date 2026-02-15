# Release v1.7.0 - Schedule Primitive

**Theme**: Time-based execution for socio-technical workflows  
**Assigned Agent**: AGENT_GEMINI  
**Depends on**: v1.6.0 (Queue BN)

## Overview

v1.7.0 adds `schedule` as a Core IR primitive, enabling declarative time-based command execution. This completes Gemini's async processing stack alongside webhooks, queues, and websockets.

## User Intent Addressed

> "If a high-priority ticket sits untouched for 4 hours, escalate to manager and post in Slack. The system should just do this—no external cron jobs, no polling scripts."

## Core IR Extension

```typescript
schedule EscalateHighPriority {
  trigger: { on_event: "TicketMovedToPending", delay: "4h" }
  condition: ticket.priority == "high" && ticket.status == "pending"
  action: command Ticket.AutoEscalate { ticket_id: event.entity_id }
  queue: ReliableQueue  // Reliable execution via queue
}
```

## Features

### 1. Cron Schedules (Recurring)
```
schedule DailySummary {
  trigger: { cron: "0 9 * * MON-FRI" }
  timezone: "America/New_York"
  action: command Report.Generate { date: schedule.scheduled_at }
}
```

### 2. Delayed Schedules (Event + Time)
```
schedule FollowUpReminder {
  trigger: { on_event: "TicketCreated", delay: "3d" }
  condition: ticket.status != "resolved"
  action: command Ticket.SendReminder { ticket_id: event.entity_id }
}
```

### 3. Conditional Execution
- Optional `condition` expression evaluated before execution
- Skip job if condition false (e.g., ticket already resolved)

### 4. Queue Integration
- Schedule can route to queue for reliable execution
- Composes with BN queue primitive (retry, DLQ)

### 5. Admin Controls
```
GET /admin/schedules              # List schedules, next runs
GET /admin/schedules/:name/jobs   # Pending jobs
POST /admin/schedules/:name/trigger  # Execute now
DELETE /admin/jobs/:id            # Cancel pending
```

## Schedule Types

| Type | Syntax | Use Case |
|------|--------|----------|
| **Cron** | `cron: "0 9 * * *"` | Daily summaries, reports |
| **Delay** | `delay: "24h"` | Timeouts, reminders |
| **Event+Delay** | `on_event: "Created", delay: "3d"` | Follow-ups, escalations |

## Architecture

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│    CRON     │     │    DELAY    │     │    EVENT    │
│  (periodic) │     │  (relative) │     │  + delay    │
└──────┬──────┘     └──────┬──────┘     └──────┬──────┘
       │                   │                   │
       └───────────────────┼───────────────────┘
                           │
                           ▼
              ┌─────────────────────┐
              │   SCHEDULED_JOBS    │
              │   (scheduled_at)    │
              └──────────┬──────────┘
                         │
              ┌──────────┴──────────┐
              ▼                     ▼
        ┌──────────┐          ┌──────────┐
        │ CONDITION│          │   QUEUE  │
        │  (eval)  │          │ (buffer) │
        └────┬─────┘          └────┬─────┘
             │                     │
             └──────────┬──────────┘
                        ▼
              ┌─────────────────┐
              │ EXECUTE COMMAND │
              └─────────────────┘
```

## Checklist

- [x] BO1.1-1.4: Core IR schedule extension
- [x] BO2.1-2.4: Schedule storage and polling
- [x] BO3.1-3.4: Execution and observability

## Database Schema

```sql
CREATE TABLE scheduled_jobs (
  id TEXT PRIMARY KEY,
  schedule_name TEXT NOT NULL,
  scheduled_at INTEGER NOT NULL,    -- When to execute
  status TEXT DEFAULT 'pending',    -- pending | running | completed | failed
  command_entity TEXT NOT NULL,
  command_name TEXT NOT NULL,
  input_json TEXT,
  queue_name TEXT                   -- Route through queue?
);
```

## Comparison

| Feature | SLA (v1.0) | Schedule (BO) |
|---------|------------|---------------|
| Tracks time? | ✅ | ✅ |
| Takes action? | ⚠️ (limited) | ✅ (any command) |
| Conditions? | ❌ | ✅ |
| Cron/recurring? | ❌ | ✅ |
| Queue integration? | ❌ | ✅ |

## Test Coverage

| Test | Description |
|------|-------------|
| Cron | Expression evaluates correctly |
| Timezone | DST transitions handled |
| Event trigger | Schedule created on event |
| Condition | Job skipped when false |
| Queue route | Message enqueued, not direct |
| Retry | Failed job retried |
| Admin | List, cancel, trigger APIs work |

## Gemini's Complete Async Stack

```
v1.4.0  BL  WebSocket  ──► Real-time client updates
v1.5.0  BM  Webhook    ──► Ingest external events  
v1.6.0  BN  Queue      ──► Reliable async execution
v1.7.0  BO  Schedule   ──► Time-based execution

        External ──webhook──► Queue ──worker──► Command
            ▲                    │
            └────schedule────────┘
                              │
        Command ──event──► WebSocket ──► Browser
```

## Future Work (v1.8.0+)

- **Business hours**: Exclude weekends/holidays
- **Rate limiting**: Max N jobs per window
- **Job chaining**: Schedule triggers schedule
- **Calendar integration**: External calendar events
