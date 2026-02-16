# AGENTS.md

This file defines how an execution agent should work on the CICSC repository.
It is not user-facing documentation. It is operational guidance for contributors
and autonomous agents executing the execution plan.

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

Lean proof baseline:
- Lean Kernel v1.5 is the coherency-complete baseline for kernel semantics.
- New semantics work must preserve the canonical evaluator/typing/WF bridges established in v1.5.

---

## Quick Reference

### Control-Plane Commands

```bash
# View assignments
./control-plane/inbox.sh [AGENT_NAME]

# Dispatch work (main agent)
./control-plane/dispatch.sh --checkbox AY1.1 --agent AGENT_KIMI

# Claim open assignments (worker)
./control-plane/claim.sh AGENT_KIMI

# Complete work (REQUIRED - updates both tracking files)
./control-plane/complete.sh AY1.1 [COMMIT_SHA]

# Validate state
./control-plane/validate.sh

# Run gate checks
./control-plane/check_gates.sh

# Add new phase
./control-plane/add_phase.sh --id BZ --number 52 --title "Title" --checkboxes "BZ1.1:desc"

# Add checkboxes to existing milestone
./control-plane/add_checkbox.sh --milestone BZ1 --checkbox "BZ1.1:description"

# Integrate feature branch
./control-plane/integrate.sh status

# Onboard agent
./control-plane/onboard.sh AGENT_KIMI
```

### Files

- `control-plane/execution-ledger.yaml` - Phase/milestone/checkbox definitions (source of truth)
- `control-plane/assignments.yaml` - Active assignments (checkbox, agent, status)

---

## Workflow

### Main Agent

1. Check current phase/milestone status in `execution-ledger.yaml`
2. Dispatch work: `./control-plane/dispatch.sh --checkbox REF --agent AGENT`
3. Commit: `git add control-plane/ && git commit -m "dispatch: REF -> AGENT"`
4. Workers pull `main`, claim, work, complete
5. Main pulls worker commits, validates state

### Worker Agent

1. `git fetch origin && git rebase origin/main`
2. Check inbox: `./control-plane/inbox.sh AGENT_NAME`
3. Claim work: `./control-plane/claim.sh AGENT_NAME`
4. Implement in your worktree on appropriate branch
5. Run gates: `./control-plane/check_gates.sh`
6. **Complete (REQUIRED):** `./control-plane/complete.sh CHECKBOX_REF`
   - This runs gates, updates `assignments.yaml` to `done`, and marks checkbox done in `execution-ledger.yaml`
   - Must be done BEFORE the final commit
7. Commit and push to **feature branch** (NOT main)
8. FF-merge into main via PR or `git merge --ff-only`

### Feature Branch Workflow

Always use feature branches, never commit directly to main:

```bash
# Create feature branch from main
git fetch origin main
git checkout -b feat/description origin/main

# Work and commit
git add -A && git commit -m "feat: description"

# Push to origin as branch
git push origin feat/description

# FF-merge into main (via PR or manually)
git checkout main
git merge --ff-only feat/description
git push origin main
```

**Why:** The FF-only categorical guarantees require all integrations to go through the boundary. Direct commits to main break the structural invariants.

---

## Deterministic Invocation Contract

If the instruction is only:

`Follow AGENTS.md`

then execute exactly this protocol:

1. `cd /home/andrey/src/cicsc`
2. Run `./control-plane/validate.sh`
3. Check inbox: `./control-plane/inbox.sh [AGENT_NAME]`
4. If open assignments exist: 
   - Claim: `./control-plane/claim.sh [AGENT_NAME]`
   - Implement the work
   - **Complete (REQUIRED):** `./control-plane/complete.sh CHECKBOX_REF` 
     (updates tracking files, must be committed)
5. If no assignments: stand down and report status
6. Return a completion report containing:
   - `checkbox_ref`
   - `commit_sha`
   - `current_status`

---

## Working Style

### 0. Canonical Execution Model (Mandatory)

Execution status truth is single-source:
- `control-plane/execution-ledger.yaml` is the only canonical status ledger.
- `PHASE*.md` files are derived views; they are not authoritative for status.
- Planning/navigation docs (for example `PHASE_LEVEL_ROADMAP.md`, `JOURNEY_VECTOR.md`)
  must not contain execution status checkboxes.

Work unit policy:
- one checkbox = one commit,
- commit message must include the checkbox ID token (for example: `phase12 ac3.2`).

Before marking a checkbox complete, run:
- `./control-plane/check_gates.sh`
- `./control-plane/validate.sh`

This gate enforces:
- execution-ledger structural integrity,
- phase-view sync with execution-ledger,
- commit-evidence presence for checked checkboxes.

### 0.1 Simplified Collaboration (Current)

The collaboration system has been simplified from a complex message-passing protocol
to direct state management:

**Previous (v1):**
- 59 scripts, 6 YAML models
- Message events, evidence bindings, role authority
- Auto-dispatch loops, circuit breakers

**Current (v2):**
- 6 scripts, 2 YAML files
- Direct assignments with 3 states: open/in_progress/done
- Git history as audit trail

**Why simplified:**
- The complexity exceeded the problem requirements
- Event sourcing without transactions caused data integrity issues
- 24,000 lines for work assignment was accidental complexity
- Git already provides history, content addressing, and concurrency control

**Migration:**
- Old system archived in git history (commits before 2026-02-15)
- New system uses same `execution-ledger.yaml` structure
- `assignments.yaml` replaces the message/collab model

---

### 1. Preserve invariants before adding features

Never add functionality that weakens:
- transactional semantics
- replay-verification guarantees
- conformance between oracle and SQL backends

If a feature cannot be implemented without weakening invariants, add:
- a typechecker restriction, or
- an explicit limitation in docs/spec.

---

### 2. Always add a conformance test for new lowering logic

If you implement any of the following:

- Query → SQL lowering
- Expr → SQL lowering
- Constraint lowering
- Reducer lowering

Then also add:

- a differential test: SQL execution vs oracle interpreter

No exceptions. If you cannot write the test, the feature is not done.

---

### 3. Do not encode bundle-specific logic in runtime

The runtime must not "know" about:
- Ticketing
- CRM
- Kanban
- any specific shadow column names

All schema, columns, indexes, and views must come from IR.

If you find yourself hardcoding column names, stop and move that logic into:
`adapters/sqlite/src/schema/gen.ts` or equivalent.

---

### 4. Fail fast at compile-time, not at runtime

Prefer:

- IR typechecker rejections
- Spec compiler errors

over:

- runtime exceptions
- SQL errors
- silent NULL propagation

If something can be detected statically, detect it statically.

---

### 5. Respect the semantic split

There are three layers. Do not collapse them:

1. **Spec DSL (user intent)**
   - ergonomic
   - may contain sugar
   - no backend assumptions

2. **Core IR (semantic truth)**
   - minimal calculus
   - backend-agnostic
   - must be fully typechecked

3. **Backend lowering**
   - SQL-specific
   - may reject unsupported constructs
   - must conform to oracle semantics

Never leak backend constraints into Spec or Core IR.
Enforce backend limits via typechecker flags or feature gates.

---

### 6. Add migrations only after type safety is strong

Do not implement migration execution until:

- IR typechecker is strict
- schema generation is deterministic
- replay verification is stable

Migrations amplify errors. They must be built on solid ground.

---

## Execution Order (Recommended)

Follow this order unless blocked:

1. IR typechecker hardening  
2. Schema generation completeness (indexes, per-version tables)  
3. SQL lowering completeness + conformance tests  
4. Bundle registry (R2/KV) + tenant binding  
5. Spec DSL sugar + compiler  
6. Migrations + cutover protocol  
7. Postgres adapter  
8. Stress verticals (CRM, Kanban)  

Do not skip steps. Each step reduces blast radius for the next.

---

## Testing Discipline

Every PR should add or extend at least one of:

- oracle tests
- SQL-vs-oracle conformance tests
- IR typechecker negative tests
- schema generation snapshot tests

If a change cannot be tested meaningfully, explain why in the PR.

---

## Error Handling Philosophy

Prefer:

- explicit errors
- structured error objects
- path-qualified error messages

Avoid:

- stringly-typed errors
- silent fallback behavior
- partial success

---

## Design Smells (Stop If You See These)

- "Let's special-case Ticketing here"
- "We'll just allow this expression in SQL"
- "Let's parse SQL back into IR"
- "We can fix this at runtime"
- "This migration is best-effort"

Each of these breaks core invariants.

---

## Definition of Done (for any TODO)

A TODO is complete only when:

- Code is implemented
- Typechecker updated (if semantics changed)
- Conformance tests added or updated
- Docs/spec updated if semantics changed
- No bundle-specific hacks introduced

---

## North Star

At completion, CICSC should allow:

> A non-programmer to describe a socio-technical control system in Spec,
> compile it, deploy it, evolve it with migrations,
> and retain invariants provably across time.

Everything you build should move the system toward that state.

---

## Collaboration System Design Notes

### Why Git for State (vs. Live Database)

The system uses Git as the source of truth for execution state. This is **intentional**, not accidental:

**Benefits:**
- **Immutable audit trail**: Every state change is permanently recorded
- **Content-addressed evidence**: Commits provide cryptographic proof of work
- **Branch isolation**: Worktrees don't interfere with each other until merge
- **No single point of failure**: Distributed by design

**Trade-off:**
- **Sync latency**: Changes in one worktree aren't visible to others until merge

This is a **consistency over availability** choice. We prefer:
- Accurate history over live updates
- Deterministic replay over real-time collaboration
- Auditability over convenience

**Pattern for Multi-Agent Work:**
```bash
# Worker: claim with sync to get latest
git fetch origin && git rebase origin/main
./control-plane/claim.sh AGENT_NAME

# Or use --sync flag:
./control-plane/claim.sh AGENT_NAME --sync

# Worker: complete work
./control-plane/complete.sh CHECKBOX_REF

# Worker: push branch
git push origin worktree-branch

# Main: merge and sync
git merge worktree-branch
./control-plane/validate.sh
```

The "fragmentation" across branches is **isolation by design**, not a bug.
