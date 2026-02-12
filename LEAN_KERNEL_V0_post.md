## Coherent forward options (post Lean Kernel v0)

You have a working Lean kernel, but it is not yet a faithful semantics for CICSC because:
- typechecker and evaluator disagree on `.get` and `.row`
- evolution proof uses a replay semantics that ignores StreamId
- bool_query is stubbed (rowsCount only)

Below are coherent paths forward. Each is internally consistent; mixing them creates drift.

---

## Option A — Alignment-First (Kernel becomes normative)
Goal: Lean is the source of truth for CICSC semantics.

### A1. Semantic alignment (must-do)
- [x] Unify replay semantics: Evolution proofs must use StreamId + inStream filtering
- [x] Unify reducer env with command env:
  - [x] define `mkRow : State → AttrMap` (canonical ordering + reserved fields)
  - [x] set `env.row := mkRow st` inside `applyReducer`
- [ ] Decide reserved keys (`state`, etc.) and enforce non-collision at IR WF layer

### A2. Typechecker alignment (must-do)
- [ ] Fix `.get` typing (choose one):
  - [ ] weak dynamic: `get : Obj → Ty` returns `.tNull` or `.tObj` and treat as total/weak
  - [ ] option types: add `tOpt` and make `get : Obj → Opt α` (bigger change)
  - [ ] schema types: object fields typed (largest change)
- [ ] Add `row.state : tString` as a primitive or VarRef (`.rowState`)

### A3. Replace stubs with semantics (incremental)
- [ ] Define relational semantics for a Query subset:
  - filter, project, orderBy, limit, offset, (no join/groupBy yet)
- [ ] Prove oracle QueryEval = relational semantics for that subset
- [ ] Reinterpret bool_query constraints against that semantics

Outcome: Lean can drive TS conformance work; proofs match runtime.

---

## Option B — Proof-First (Migrations + invariants as the main artifact)
Goal: keep kernel small; prove the commuting diagram for a realistic migration class.

### B1. Freeze kernel semantics as “minimal calculus”
- [ ] Restrict Expr to total operators with simple typing (drop `.get` or make it untyped)
- [ ] Restrict Query out of kernel (treat bool_query as axiom/spec obligation)

### B2. Make migrations constructive and prove naturality strongly
- [ ] Define a concrete migration class:
  - eventType renames
  - payload field renames/defaults (optional)
  - state label renames
- [ ] Prove step-commutation lemma
- [ ] Prove replay commutes for all histories (induction)
- [ ] Prove snapshot constraint preservation under this migration class

Outcome: Lean becomes a migration correctness engine; less about full CICSC semantics.

---

## Option C — Spec/IR WF-First (Typechecker theorems, not full semantics)
Goal: formalize the static guarantees that match the TS IR typechecker.

### C1. Define `WF(IR)` as a Prop mirroring TS checks
- [ ] reducer writes only declared attrs/shadows
- [ ] state transitions remain in `states`
- [ ] commands emit only known event types
- [ ] views/constraints reference only legal fields
- [ ] SQL-lowerable fragment constraints (if you keep it)

### C2. Prove meta-theorems
- [ ] `WF(IR) → replay preserves WF(State)`
- [ ] `WF(IR) → command execution preserves WF(State)` (pure semantics)
- [ ] `WF(IR) → constraints decidable` (snapshot constraints)

Outcome: Lean becomes the formal backing for the static layer, complementing runtime tests.

---

## Option D — Extract “Kernel Spec” as a contract and stop proving implementation details
Goal: Lean produces a stable spec; TS and backends satisfy it via testing.

- [ ] Define a formal “Kernel Spec” (types + semantics)
- [ ] State conformance obligations (oracle equivalence, migration commutation)
- [ ] Provide example proofs for representative fragments
- [ ] Everything else is engineering + tests

Outcome: Lean defines the theory; implementation is validated by conformance suites.

---

## Recommendation (most coherent with your stated objective)
Pick **Option A (Alignment-First)**, then branch into B for migrations.

Reason: CICSC’s claim is “executable socio-technical system compiler with invariant-preserving evolution”.
That requires the kernel semantics and the evolution semantics to be the same thing.

---
