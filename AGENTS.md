# AGENTS.md

This file defines the CICSC execution agent system. See role-specific guides:

- [AGENTS_MAIN.md](AGENTS_MAIN.md) - Main agent orchestration
- [AGENTS_WORKER.md](AGENTS_WORKER.md) - Worker agent implementation

---

## Mission

Turn CICSC from a working substrate prototype into:

> A correct, invariant-preserving compiler + runtime for socio-technical systems,
> with a real user intent DSL and migration guarantees.

Primary success criteria:

- Invariants hold under concurrency.
- IR and runtime semantics are aligned and enforced by typechecking + conformance tests.
- Spec DSL is usable by humans.
- Migrations are executable and replay-verified.
- Backends (SQLite/D1, Postgres) are semantically equivalent to the oracle.

---

## Control-Plane Scripts

```bash
./control-plane/validate.sh                 # Validate state
./control-plane/check_gates.sh              # Run gates
./control-plane/add_phase.sh --number N --title "T"
./control-plane/add_milestone.sh --phase CH --title "Milestone title"
./control-plane/add_checkbox.sh --milestone X --checkbox "X1.1:desc"
./control-plane/plan_work.sh --phase-title "T" --milestone-title "M" --checkbox "desc"

# Mechanistic core (runs continuously)
./control-plane/autoassign.sh --loop         # Assigns open work to standing_by agents with fresh heartbeat

# Worker (runs continuously)
./control-plane/agentd.sh run --agent AGENT_CODEX
./control-plane/agentd.sh stop --agent AGENT_CODEX
./control-plane/agentd.sh unblock --agent AGENT_CODEX --reason "manual_unblock"
./control-plane/status.sh --agent AGENT_CODEX --json
./control-plane/status.sh --all --json
./control-plane/status.sh --summary --json
./control-plane/worker-run-assignment.sh --agent AGENT_CODEX --checkbox CH1.1

# Integration boundary
./control-plane/integrate.sh integrate X1.1 --agent AGENT_CODEX
```

---

## Architecture

```
Human Main:          adds work to ledger (open)
                         ↓
autoassign.sh:       assigns open → standing_by+heartbeat agents (LIFO)
                         ↓
agentd.sh:           blocking daemon loop (heartbeat/lease/close)
                         ↓
worker-run-assignment.sh: gates → push verify → integrate
                         ↓
integrate.sh:        closes assigned checkbox as done (with commit evidence)
                         ↓
validate.sh:         verifies state
```

- Pull-based: workers pull from SQLite ledger state
- Mechanistic core: autoassign handles assignment + stale reclaim
- Agent identity: explicit `--agent <AGENT_ID>` on daemon commands

---

## Files

- `state/ledger.db` - SQLite database with phases, milestones, checkboxes, assignments, agents

---

## North Star

At completion, CICSC should allow:

> A non-programmer to describe a socio-technical control system in Spec,
> compile it, deploy it, evolve it with migrations,
> and retain invariants provably across time.
