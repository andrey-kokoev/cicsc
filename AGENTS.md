# AGENTS.md

This file defines how an execution agent should work on the CICSC repository.
It is not user-facing documentation. It is operational guidance for contributors
and autonomous agents executing the roadmap.

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

## Working Style

### 0. Canonical Execution Model (Mandatory)
Execution status truth is single-source:
- `ROADMAP.md` is the only canonical status ledger.
- `PHASE*.md` files are derived views; they are not authoritative for status.

Work unit policy:
- one checkbox = one commit,
- commit message must include the checkbox ID token (for example: `phase12 ac3.2`).

Before marking a checkbox complete, run:
- `./scripts/check_canonical_execution_model.sh`

This gate enforces:
- roadmap structural integrity,
- phase-view sync with roadmap,
- commit-evidence presence for checked checkboxes.

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
The runtime must not “know” about:
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

- “Let’s special-case Ticketing here”
- “We’ll just allow this expression in SQL”
- “Let’s parse SQL back into IR”
- “We can fix this at runtime”
- “This migration is best-effort”

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
