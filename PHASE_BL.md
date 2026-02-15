# Phase BL: Real-time / WebSockets - Live Updates

**Status**: IN PROGRESS (v1.4.0)  
**Agent**: AGENT_GEMINI  
**Goal**: Enable real-time updates with declarative subscriptions in Spec DSL

## User Intent Scenario

**Alex** (Kanban board user):
> "When Sarah moves a task to 'In Progress', I want my board to update instantly—no refresh. And I want to see who's editing what so we don't step on each other."

**Current State**: Poll `/tasks` every 5 seconds. Laggy, wasteful, no presence awareness.  
**Desired State**: Instant push updates, collaborative cursors, live presence.

## Acceptance Criteria

1. Declare in Spec: `subscription TaskUpdates: view ActiveTasks`
2. Client connects: `ws://api/tasks/live`
3. Changes pushed instantly with minimal latency (<100ms)
4. Automatic reconnection on disconnect
5. Missed events replayed during reconnect window

## Spec DSL Design

```
app RealtimeKanban {
  entity Task {
    attr title: string
    attr status: "todo" | "doing" | "done"
    attr assignee: ref User
  }
  
  view ActiveTasks: Task where status != "done"
  
  // Live subscription to view changes
  subscription TaskUpdates: view ActiveTasks
  
  // Live subscription to specific instance
  subscription TaskDetail: Task by id
}
```

## Architecture

```
┌─────────────┐      WebSocket       ┌──────────────┐
│   Client    │ ◄──────────────────► │  Connection  │
│  (Browser)  │   wss://.../live     │   Manager    │
└──────┬──────┘                      └──────┬───────┘
       │                                    │
       │  1. SUBSCRIBE TaskUpdates          │
       │  2. PING/PONG keepalive            │
       │  3. EVENT {task, change_type}      │
       │                                    │
       │                         ┌──────────▼──────────┐
       │                         │   Subscription      │
       │                         │      Registry       │
       │                         │  (query → clients)  │
       │                         └──────────┬──────────┘
       │                                    │
       │                         ┌──────────▼──────────┐
       │                         │   Event Broadcaster │
       └────────────────────────►│   (database hooks)  │
                                 └─────────────────────┘
```

## Message Protocol

```typescript
// Client → Server
{type: "subscribe", subscription: "TaskUpdates", filter?: {...}}
{type: "unsubscribe", subscription: "TaskUpdates"}
{type: "ping", timestamp: number}

// Server → Client  
{type: "subscribed", subscription: "TaskUpdates", initial: [...]}
{type: "event", subscription: "TaskUpdates", operation: "insert|update|delete", data: {...}}
{type: "pong", timestamp: number}
{type: "error", code: "AUTH_REQUIRED|INVALID_FILTER|RATE_LIMITED"}
```

## Technical Decisions

1. **WebSocket vs SSE**: WebSocket for bidirectional (presence, typing indicators)
2. **Authentication**: Token in query param (ws://...?token=xxx) - headers not available in WebSocket handshake
3. **Scaling**: Redis Pub/Sub for multi-server broadcast (future)
4. **Backpressure**: Drop events if client buffer full, log warning
5. **Replay Buffer**: Last 100 events per subscription, 30s window

## Milestones

### BL1: Spec DSL Extension for Real-time
- [x] **BL1.1**: Add 'subscription' keyword to Spec DSL for real-time queries
- [x] **BL1.2**: Define subscription filters (watch specific entity instances)  
- [x] **BL1.3**: Parse subscriptions to Core IR
- [x] **BL1.4**: Generate WebSocket endpoint schema from Spec

### BL2: WebSocket Server Implementation
- [x] **BL2.1**: WebSocket server with connection upgrade handling
- [x] **BL2.2**: Connection manager (track active subscriptions per client)
- [x] **BL2.3**: Broadcast events to subscribed clients
- [x] **BL2.4**: Authentication over WebSocket (token validation on connect)

### BL3: Client SDK & Reconnection
- [x] **BL3.1**: Client-side subscription API (subscribe/unsubscribe)
- [x] **BL3.2**: Automatic reconnection with exponential backoff
- [x] **BL3.3**: Message delivery acknowledgment
- [x] **BL3.4**: Handle missed events during disconnect (replay buffer)

## Test Plan

1. **Unit**: Connection manager tracks/drops clients correctly
2. **Integration**: Full flow - subscribe → mutate → receive event
3. **Load**: 10k concurrent connections, measure latency
4. **Chaos**: Network partition, verify reconnection + replay

## Related

- PHASE_BK (Webhooks) for "server-to-server" real-time
- PHASE_BJ (Blob Storage) v1.3.0 foundation
