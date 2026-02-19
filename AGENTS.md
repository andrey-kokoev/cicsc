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
./control-plane/add_phase.sh --id X --number N --title "T"
./control-plane/add_checkbox.sh --milestone X --checkbox "X1.1:desc"

# Mechanistic core (runs continuously)
./control-plane/autoassign.sh --loop         # Assigns open work to idle agents

# Worker (runs continuously)
./control-plane/standby.sh                  # Poll for assigned work (set AGENT_ID env)

# Integration boundary
./control-plane/integrate.sh integrate X1.1

# Legacy
./control-plane/onboard.sh [--main|--worker]
```

---

## Architecture

```
Human Main:          adds work to ledger (open)
                         ↓
autoassign.sh:       assigns open → idle agents (LIFO)
                         ↓
standby.sh:          polls, outputs when work assigned
                         ↓
Agent:               does work, commits, pushes
                         ↓
integrate.sh:        marks checkbox done
                         ↓
validate.sh:         verifies state
```

- Pull-based: workers pull from ledger
- Mechanistic core: autoassign handles assignment
- Agent identity: set via AGENT_ID env var

---

## Files

- `state/ledger.db` - SQLite database with phases, milestones, checkboxes, assignments, agents

---

## North Star

At completion, CICSC should allow:

> A non-programmer to describe a socio-technical control system in Spec,
> compile it, deploy it, evolve it with migrations,
> and retain invariants provably across time.
