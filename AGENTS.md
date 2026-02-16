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
./control-plane/inbox.sh [AGENT_NAME]      # View assignments
./control-plane/dispatch.sh --checkbox X --agent Y  # Assign work
./control-plane/claim.sh AGENT              # Claim assignments
./control-plane/complete.sh CHECKBOX        # Complete work
./control-plane/validate.sh                 # Validate state
./control-plane/check_gates.sh              # Run gates
./control-plane/add_phase.sh --id X --number N --title "T"
./control-plane/add_checkbox.sh --milestone X --checkbox "X1.1:desc"
./control-plane/integrate.sh status
./control-plane/onboard.sh [--main] AGENT
```

---

## Files

- `control-plane/execution-ledger.yaml` - Phase/milestone/checkbox definitions (source of truth)
- `control-plane/assignments.yaml` - Active assignments

---

## North Star

At completion, CICSC should allow:

> A non-programmer to describe a socio-technical control system in Spec,
> compile it, deploy it, evolve it with migrations,
> and retain invariants provably across time.
