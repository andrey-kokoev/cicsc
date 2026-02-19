# AGENTS_WORKER.md

Worker agent implementation guide. See [AGENTS.md](AGENTS.md) for overview.

---

## Role

Run as a long-lived daemon that continuously:

1. heartbeats,
2. picks assigned work,
3. executes `worker-run-assignment` closure flow,
4. returns to `standing_by`.

---

## Execution Discipline

Non-negotiable operating model for worker agents:

1. Exactly one daemon process per agent ID.
2. Stop only on explicit stop (`agentd.sh stop`) or hard blocker.
3. On blocker, remain `blocked` with explicit reason until `agentd.sh unblock`.
4. Assignment closure is daemon-owned: gates -> push verify -> integrate.
5. Run in one foreground daemon session; do not spawn duplicate daemon terminals.

`idle` in protocol terms means `standing_by` with no assigned checkbox.

---

## Quick Reference

<!-- generated:worker_quick_reference:start -->
```bash
# Set your agent ID (do once)
export AGENT_ID=AGENT_GEMINI

# Start daemon (blocking loop)
./control-plane/agentd.sh run --agent "$AGENT_ID"

# Check authoritative status
./control-plane/status.sh --agent "$AGENT_ID" --json
./control-plane/status.sh --summary --json

# Stop daemon gracefully
./control-plane/agentd.sh stop --agent "$AGENT_ID"
```
<!-- generated:worker_quick_reference:end -->

---

## Workflow

### 1. Sync

```bash
git fetch origin && git rebase origin/main
```

### 2. Start Daemon

```bash
export AGENT_ID=AGENT_GEMINI
./control-plane/agentd.sh run --agent "$AGENT_ID"
```

Daemon behavior:

1. Writes heartbeat + lease.
2. Executes assigned checkbox via `worker-run-assignment.sh`.
3. Closes assignment through `integrate.sh`.
4. Returns to `standing_by` or `blocked`.

### 3. Observe / Control

```bash
./control-plane/status.sh --agent "$AGENT_ID"
./control-plane/agentd.sh stop --agent "$AGENT_ID"
./control-plane/agentd.sh unblock --agent "$AGENT_ID" --reason "manual_unblock"
```

---

## Important Rules

1. Never edit state directly.
2. Never commit to `main`.
3. Closure gates are enforced by `worker-run-assignment.sh`.
4. Worker daemon closes assignments; Main merges to `main`.
5. Blocked agents keep assignment ownership until explicit unblock.

---

## Common Tasks

| Task | Command |
|------|---------|
| Sync | `git fetch origin && git rebase origin/main` |
| Run daemon | `./control-plane/agentd.sh run --agent AGENT_GEMINI` |
| Status | `./control-plane/status.sh --agent AGENT_GEMINI --json` |
| Stop | `./control-plane/agentd.sh stop --agent AGENT_GEMINI` |
| Unblock | `./control-plane/agentd.sh unblock --agent AGENT_GEMINI --reason "manual_unblock"` |

---

## Notes

- Assignment protocol state is authoritative in `state/ledger.db`.
