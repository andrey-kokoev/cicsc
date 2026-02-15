# Release v1.4.0 - Real-time / WebSockets

**Theme**: Live updates and collaborative experiences  
**Assigned Agent**: AGENT_GEMINI

## Overview

v1.4.0 adds real-time capabilities to CICSC, enabling instant push updates from server to clients via WebSockets. This unlocks collaborative features like live Kanban boards, presence indicators, and real-time notifications.

## User Intent Addressed

> "When Sarah moves a task to 'In Progress', I want my board to update instantly—no refresh. And I want to see who's editing what so we don't step on each other."

## Features

### 1. Declarative Subscriptions (Spec DSL)
```
subscription TaskUpdates: view ActiveTasks
subscription TaskDetail: Task by id
```

### 2. WebSocket Server
- Connection management with subscription registry
- Authentication via token query parameter
- Efficient broadcast to subscribed clients
- Heartbeat/ping-pong keepalive

### 3. Client SDK
- Simple subscribe/unsubscribe API
- Automatic reconnection with exponential backoff
- Message acknowledgment
- Missed event replay during reconnect window

### 4. Message Protocol
```typescript
{type: "event", subscription: "TaskUpdates", operation: "update", data: {...}}
```

## Technical Highlights

- **WebSocket over SSE**: Bidirectional for presence/typing indicators
- **Scaling Path**: Redis Pub/Sub for multi-server (future)
- **Backpressure**: Drop events if client buffer full
- **Replay Buffer**: Last 100 events, 30s window

## Checklist

- [x] BL1.1-1.4: Spec DSL extension
- [x] BL2.1-2.4: WebSocket server implementation
- [x] BL3.1-3.4: Client SDK and reconnection

## Future Work (v1.5.0+)

- Multi-server scaling with Redis Pub/Sub
- Presence/typing indicators
- Collaborative cursors
- Conflict-free Replicated Data Types (CRDTs)
