# Phase BO: Schedule Primitive - Time-Based Execution

**Status**: PLANNED (v1.7.0)  
**Agent**: AGENT_GEMINI  
**Goal**: Add `schedule` as a Core IR primitive for time-based command execution

## Problem Statement

Current CICSC handles **event-driven** workflows well (command → event → state change). But socio-technical systems need **time-driven** workflows:

| Need | Example | Current State |
|------|---------|---------------|
| Escalation | "Escalate ticket if pending 24h" | Manual or external cron |
| Reminders | "Send follow-up email in 3 days" | Not possible |
| Recurring | "Daily summary at 9am" | External scheduler |
| Timeouts | "Auto-close inactive tickets" | SLA tracks, doesn't act |
| Business hours | "Only alert during work hours" | Hardcoded in logic |

## User Intent

**Alex** (support manager):
> "I want to declare: 'If a high-priority ticket sits untouched for 4 hours, escalate to manager and post in Slack.' The system should just do this—no external cron jobs, no polling scripts."

## Solution: Schedule Primitive

```
┌─────────────────────────────────────────────────────────────────┐
│                     SCHEDULE ENGINE                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   ┌──────────┐     ┌──────────┐     ┌──────────┐               │
│   │   CRON   │     │  DELAY   │     │  EVENT   │               │
│   │Recurring │     │ Relative │     │ + Delay  │               │
│   │(9am M-F) │     │ (3 days) │     │(24h from │               │
│   └────┬─────┘     └────┬─────┘     │ created) │               │
│        │                │           └────┬─────┘               │
│        └────────────────┼────────────────┘                      │
│                         │                                       │
│                         ▼                                       │
│              ┌─────────────────────┐                           │
│              │   SCHEDULED_JOBS    │                           │
│              │   (scheduled_at)    │                           │
│              └──────────┬──────────┘                           │
│                         │                                       │
│              ┌──────────┴──────────┐                           │
│              ▼                     ▼                           │
│        ┌──────────┐          ┌──────────┐                     │
│        │   DUE    │          │  QUEUE   │                     │
│        │  (now)   │          │ (buffer) │                     │
│        └────┬─────┘          └────┬─────┘                     │
│             │                     │                            │
│             └──────────┬──────────┘                            │
│                        ▼                                       │
│              ┌─────────────────┐                              │
│              │ EXECUTE COMMAND │                              │
│              │  (with context) │                              │
│              └─────────────────┘                              │
└─────────────────────────────────────────────────────────────────┘
```

## Core IR Extension

```typescript
// core/ir/types.ts additions
export type CoreIrV0 = {
  // ... existing: types, queues, webhooks, subscriptions
  schedules?: Record<string, ScheduleSpecV0>
}

export type ScheduleSpecV0 = {
  // When to trigger
  trigger: ScheduleTriggerV0
  
  // Optional: only fire if condition true
  condition?: ExprV0
  
  // What to execute
  action: ScheduleActionV0
  
  // Optional: route through queue for reliability
  queue?: string
  
  // Execution config
  execution: {
    timezone?: string                // "America/New_York", default UTC
    max_delay_seconds?: number       // Tolerance for late execution
    retry?: {
      max_attempts: number
      backoff_ms: number
    }
  }
}

export type ScheduleTriggerV0 =
  | { cron: string }                           // "0 9 * * MON-FRI"
  | { delay_seconds: number }                  // Fixed delay
  | { delay_expr: ExprV0 }                     // Computed: "now + 24h"
  | { on_event: string; delay_seconds?: number } // Event-triggered + optional delay

export type ScheduleActionV0 = {
  entity_type: string
  command: string
  input_map: Record<string, ExprV0>  // Can reference: schedule.scheduled_at, event.*
}
```

## Spec DSL Design

```
app TicketSystem {
  entity Ticket {
    attr created_at: time
    attr status: "open" | "pending" | "resolved"
    attr priority: "low" | "medium" | "high"
    attr last_activity_at: time
    
    command AutoEscalate {
      input { ticket_id: string, reason: string }
      guard: true
      emit Escalated { to: "manager" }
    }
    
    command SendReminder {
      input { ticket_id: string }
      guard: status != "resolved"
      emit ReminderSent
    }
    
    command AutoClose {
      input { ticket_id: string }
      guard: status != "resolved"
      emit AutoClosed
    }
  }
  
  // CRON: Recurring daily summary
  schedule DailyTicketSummary {
    trigger: { cron: "0 9 * * MON-FRI" }
    timezone: "America/New_York"
    action: command Report.GenerateSummary {
      date: schedule.scheduled_at,
      ticket_count: count(Ticket where status != "resolved")
    }
  }
  
  // DELAY: Follow-up reminder after 3 days
  schedule FollowUpReminder {
    trigger: { on_event: "TicketCreated", delay: "3d" }
    condition: ticket.status != "resolved"
    action: command Ticket.SendReminder {
      ticket_id: event.entity_id
    }
    queue: ReliableQueue  // Ensure delivery
  }
  
  // TIMEOUT: Escalate high-priority tickets pending too long
  schedule EscalateHighPriority {
    trigger: { on_event: "TicketMovedToPending", delay: "4h" }
    condition: ticket.priority == "high" && ticket.status == "pending"
    action: command Ticket.AutoEscalate {
      ticket_id: event.entity_id,
      reason: "high_priority_timeout"
    }
  }
  
  // INACTIVITY: Auto-close if no activity for 30 days
  schedule AutoCloseInactive {
    trigger: { on_event: "LastActivity", delay: "30d" }
    condition: ticket.status != "resolved"
    action: command Ticket.AutoClose {
      ticket_id: event.entity_id
    }
  }
}
```

## Database Schema

```sql
-- Scheduled jobs (one row per scheduled execution)
CREATE TABLE scheduled_jobs (
  id TEXT PRIMARY KEY,                    -- UUID
  schedule_name TEXT NOT NULL,            -- Reference to schedule spec
  
  -- Trigger context
  trigger_type TEXT NOT NULL,             -- "cron" | "delay" | "event"
  entity_type TEXT,                       -- For event-triggered
  entity_id TEXT,                         -- For event-triggered
  event_type TEXT,                        -- For event-triggered
  
  -- Timing
  scheduled_at INTEGER NOT NULL,          -- Unix ms when to execute
  timezone TEXT,                          -- "America/New_York", etc.
  
  -- Action
  command_entity TEXT NOT NULL,
  command_name TEXT NOT NULL,
  input_json TEXT NOT NULL,
  
  -- Optional queue routing
  queue_name TEXT,
  
  -- Execution state
  status TEXT DEFAULT 'pending',          -- pending | running | completed | failed | cancelled
  attempts INTEGER DEFAULT 0,
  
  -- Result
  executed_at INTEGER,
  result_json TEXT,
  error TEXT,
  
  -- Metadata
  created_at INTEGER NOT NULL,
  created_by TEXT                         -- "cron" | event_id | "api"
);

-- Index for efficient polling
CREATE INDEX idx_scheduled_pending ON scheduled_jobs(scheduled_at, status) 
  WHERE status IN ('pending', 'running');

-- Index for entity lookup (cancel jobs when entity deleted)
CREATE INDEX idx_scheduled_entity ON scheduled_jobs(entity_type, entity_id);

-- Cron schedule state (for recurring)
CREATE TABLE cron_schedules (
  name TEXT PRIMARY KEY,
  expression TEXT NOT NULL,               -- "0 9 * * MON-FRI"
  timezone TEXT,
  last_run_at INTEGER,
  next_run_at INTEGER NOT NULL
);
```

## Runtime Architecture

### Components

```
┌─────────────────────────────────────────────────────────────────┐
│                     SCHEDULE ENGINE                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │  CRON SCHEDULER (periodic execution)                      │ │
│  │  - Runs every minute (or via Cloudflare Cron Trigger)     │ │
│  │  - Computes next_run_at from cron expression              │ │
│  │  - Enqueues jobs to scheduled_jobs table                  │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │  EVENT INTERCEPTOR (hooks into command execution)         │ │
│  │  - After command emits event                              │ │
│  │  - Checks for schedules with on_event trigger             │ │
│  │  - Creates scheduled job with delay                       │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                  │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │  SCHEDULE WORKER (polls for due jobs)                     │ │
│  │  - Query: SELECT * FROM scheduled_jobs                    │ │
│  │           WHERE status='pending'                          │ │
│  │           AND scheduled_at <= now                         │ │
│  │           ORDER BY scheduled_at                           │ │
│  │           LIMIT 10                                        │ │
│  │  - For each job:                                          │ │
│  │    1. Evaluate condition expression                       │ │
│  │    2. If true: execute action or enqueue to queue         │ │
│  │    3. Mark completed/failed                               │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Schedule Worker Pseudocode

```typescript
// runtime/schedule/worker.ts
export class ScheduleWorker {
  constructor(
    private store: ScheduleStore,
    private ir: CoreIrV0,
    private commandExecutor: CommandExecutor,
    private queueStore?: QueueStore
  ) {}

  async pollAndExecute(batchSize: number = 10) {
    const dueJobs = await this.store.getDueJobs(batchSize)
    
    for (const job of dueJobs) {
      await this.executeJob(job)
    }
  }

  private async executeJob(job: ScheduledJob) {
    const scheduleSpec = this.ir.schedules![job.schedule_name]
    
    // Evaluate condition if present
    if (scheduleSpec.condition) {
      const conditionMet = await this.evaluateCondition(
        scheduleSpec.condition,
        job
      )
      if (!conditionMet) {
        await this.store.markSkipped(job.id, "condition_false")
        return
      }
    }
    
    // Build command input
    const input = this.transformInput(scheduleSpec.action.input_map, job)
    
    // Execute: direct or via queue
    if (scheduleSpec.queue && this.queueStore) {
      // Enqueue for reliable execution
      await this.queueStore.enqueue(scheduleSpec.queue, {
        type: "scheduled_action",
        schedule_name: job.schedule_name,
        command: scheduleSpec.action,
        input
      })
      await this.store.markQueued(job.id)
    } else {
      // Direct execution
      try {
        const result = await this.commandExecutor.execute({
          entity_type: scheduleSpec.action.entity_type,
          command_name: scheduleSpec.action.command,
          input
        })
        await this.store.markCompleted(job.id, result)
      } catch (error) {
        await this.handleFailure(job, error)
      }
    }
  }

  private async handleFailure(job: ScheduledJob, error: Error) {
    const scheduleSpec = this.ir.schedules![job.schedule_name]
    const maxAttempts = scheduleSpec.execution.retry?.max_attempts ?? 1
    
    if (job.attempts < maxAttempts) {
      const backoff = scheduleSpec.execution.retry!.backoff_ms * Math.pow(2, job.attempts)
      await this.store.retry(job.id, backoff)
    } else {
      await this.store.markFailed(job.id, error)
    }
  }
}
```

## Cron Expression Support

Using standard cron syntax with extensions:

```
┌───────────── minute (0 - 59)
│ ┌───────────── hour (0 - 23)
│ │ ┌───────────── day of month (1 - 31)
│ │ │ ┌───────────── month (1 - 12)
│ │ │ │ ┌───────────── day of week (0 - 6) (Sunday=0)
│ │ │ │ │
│ │ │ │ │
* * * * *  → Every minute
0 * * * *  → Every hour
0 9 * * MON-FRI  → 9am weekdays
0 9 1 * *  → 9am on 1st of month
*/5 9-17 * * MON-FRI  → Every 5 min during business hours
```

## Integration with Queue (BN)

```
┌─────────────────────────────────────────────────────────────────┐
│                    COMPOSED EXECUTION                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   Time ──► Schedule ──► Condition? ──► Queue ──► Command        │
│                          (true)                                  │
│                            │                                     │
│                            ▼                                     │
│                         (false)                                  │
│                          Skip                                    │
│                                                                  │
│   Schedule provides:                                            │
│   - Timing (when)                                               │
│   - Condition (whether)                                         │
│                                                                  │
│   Queue provides:                                               │
│   - Buffering (capacity)                                        │
│   - Retry (reliability)                                         │
│   - DLQ (observability)                                         │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## Admin API

```typescript
// GET /admin/schedules?tenant_id=...
{
  "schedules": [
    {
      "name": "DailyTicketSummary",
      "trigger": { "cron": "0 9 * * MON-FRI" },
      "next_run": "2026-02-16T09:00:00-05:00",
      "pending_jobs": 1
    },
    {
      "name": "EscalateHighPriority", 
      "trigger": { "on_event": "TicketMovedToPending", "delay": "4h" },
      "pending_jobs": 5
    }
  ]
}

// GET /admin/schedules/:name/jobs?status=pending
{
  "jobs": [
    {
      "id": "job_abc123",
      "scheduled_at": 1708101600000,
      "entity_type": "Ticket",
      "entity_id": "T-456",
      "status": "pending"
    }
  ]
}

// POST /admin/schedules/:name/trigger (manual run)
{ "ok": true, "job_id": "job_xyz789" }

// DELETE /admin/jobs/:id (cancel pending job)
{ "ok": true }

// POST /admin/jobs/:id/retry (retry failed job)
{ "ok": true, "new_job_id": "job_def456" }
```

## Comparison: SLAs vs Schedules

| Feature | SLA (v1.0) | Schedule (BO) |
|---------|------------|---------------|
| **Purpose** | Track time bounds | Act on time events |
| **Trigger** | Event + time window | Time or event + delay |
| **Action** | Emit event or auto-transition | Execute any command |
| **Flexibility** | Fixed patterns | Arbitrary expressions |
| **Composes** | Standalone | With queue for reliability |

```
SLA:    "Alert me if ticket pending > 24h"
        (track, notify)

Schedule: "Escalate ticket if pending > 24h"  
          (act, change state, trigger workflow)
```

## Milestones

### BO1: Core IR Schedule Extension
- [x] **BO1.1**: Add ScheduleSpecV0 to Core IR (cron, delay, action)
- [x] **BO1.2**: Define schedule trigger types (cron, delay, event+delay)
- [x] **BO1.3**: Add schedule-to-command input mapping expressions
- [x] **BO1.4**: Update IR validator for schedule specifications

### BO2: Schedule Storage & Polling
- [x] **BO2.1**: Scheduled jobs table schema (scheduled_at, status, action)
- [x] **BO2.2**: Cron schedule tracker (last_run, next_run computation)
- [x] **BO2.3**: Schedule worker polling (due jobs query)
- [x] **BO2.4**: Event-triggered schedule creation (on event, enqueue delayed job)

### BO3: Execution & Observability
- [x] **BO3.1**: Schedule execution engine (direct or via queue)
- [x] **BO3.2**: Retry policy for failed scheduled jobs
- [x] **BO3.3**: Schedule admin API (list, cancel, trigger now)
- [x] **BO3.4**: Schedule metrics (pending count, execution latency)

## Acceptance Criteria

1. Cron schedule creates jobs at correct times (respecting timezone)
2. Event-triggered schedule creates job with delay after event
3. Condition expression evaluated before execution
4. Schedule can route through queue for reliable execution
5. Failed scheduled jobs retried with backoff
6. Admin API can list pending jobs and cancel them
7. Manual trigger API executes schedule immediately
8. Schedule metrics available (pending count, avg latency)

## Test Plan

| Test | Description |
|------|-------------|
| **Cron** | Expression "0 * * * *" creates job at top of hour |
| **Timezone** | "0 9 * * *" with America/NY runs at 9am NY time |
| **Event trigger** | TicketCreated → schedule job 3 days later |
| **Condition** | Job skipped if condition evaluates false |
| **Queue routing** | Schedule with queue → message enqueued, not direct |
| **Retry** | Failed job retried with exponential backoff |
| **Cancel** | DELETE /admin/jobs/:id removes pending job |
| **Manual trigger** | POST /admin/schedules/:name/trigger executes now |
| **DST** | Cron handles daylight saving time transitions |

## Gemini's Async Stack

| Phase | Primitive | Purpose |
|-------|-----------|---------|
| **BL** | WebSocket | Real-time client updates |
| **BM** | Webhook | Ingest external events |
| **BN** | Queue | Reliable async execution |
| **BO** | Schedule | Time-based execution (this phase) |

```
┌─────────────────────────────────────────────────────────────┐
│                  GEMINI'S ASYNC DOMAIN                       │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│   External ──webhook──► Queue ──worker──► Command           │
│       ▲                      │                              │
│       │                      │                              │
│       └────schedule──────────┘                              │
│       (time-triggered)                                      │
│                                                              │
│   Command ──event──► WebSocket ──► Browser (live)           │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

## Future Extensions

- **Business hours**: `business_hours { timezone, holidays }` modifier
- **Rate limiting**: Max N scheduled jobs per time window
- **Job chaining**: On schedule completion, trigger another schedule
- **Schedule views**: Query "all tickets with pending escalation"
- **Calendar integration**: Schedule based on external calendar events
