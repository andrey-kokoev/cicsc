# Phase BR: Native SLA Declaration

**Status**: PLANNED (v1.7.0)  
**Agent**: TBD  
**Vertical Gap**: SLA via shadows/commands workaround

## Problem

Current: SLAs modeled manually via shadows
```python
entity Ticket {
  attr sla_deadline: time  # Shadow
  command Create {
    emit TicketCreated { sla_deadline: now + 4h }
  }
}
```

Gap: First-class SLA primitive
```python
slas {
  FirstResponse {
    on: Ticket
    start: event Created
    stop: event FirstResponseSent
    within: 4h
    breach_action: command Escalate
  }
}
```

## Core IR

```typescript
export type SlaSpecV0 = {
  on_type: string
  start: { event: string; where?: ExprV0 }
  stop: { event: string; where?: ExprV0 }
  within_seconds: number
  timezone?: string
  breach_action?: {
    command: string
    input_map: Record<string, ExprV0>
  }
}
```

## Milestones

### BR1: Core IR Extension
- [x] BR1.1: SlaSpecV0 with start/stop selectors
- [x] BR1.2: SLA breach detection logic
- [x] BR1.3: Breach action binding
- [x] BR1.4: Update IR validator

### BR2: SLA Runtime
- [x] BR2.1: SLA tracker (start timers)
- [x] BR2.2: Breach detector
- [x] BR2.3: Breach action executor
- [x] BR2.4: SLA metrics export
