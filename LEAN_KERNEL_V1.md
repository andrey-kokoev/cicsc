# LEAN_KERNEL_V1.md
## CICSC Lean Kernel v1 Milestone

Lean Kernel v1 upgrades the v0 model from “exists + proves a commuting theorem under auxiliary semantics” to “faithful kernel semantics for CICSC’s executable substrate on a defined fragment”.

v1 is defined by **alignment**, **tightened typing**, and **non-stub query semantics** for a minimal subset.

---

## 0. v1 Scope

### In scope (must be faithful)
- Expr semantics + typing for the v1 fragment
- Replay semantics (StreamId filtering) used everywhere, including Evolution
- Reducer env construction (row/state) consistent across Commands, Replay, Constraints
- Snapshot constraints semantics
- Migration class: event type rename + state label rename (no payload transforms in v1)
- Naturality theorem for the migration class using the real replay semantics

### Out of scope (explicitly not proved in v1)
- SQL / SQLite / D1 semantics
- Postgres semantics
- Concurrency
- Full Query algebra (joins, groupBy)
- bool_query constraints beyond a defined subset (see §6)

---

## 1. Alignment Fixes (Semantics Coherence)

### 1.1 Canonical row construction
- [x] Add `mkRow : State → AttrMap` in `Cicsc/Core/Semantics/Common.lean` (new)
  - includes reserved `"state"` exactly once
  - defines precedence and forbids collisions
- [x] Use `mkRow` in:
  - [x] `Core/Semantics/Commands.lean` (`commandRow` removed or becomes wrapper)
  - [x] `Core/Semantics/Replay.lean` (set `env.row := mkRow st`)
  - [x] `Core/Semantics/Constraints.lean` (snapshot constraint env uses `mkRow st`)

### 1.2 Reserved field rule
- [x] Define reserved keys: `["state"]` (v1)
- [x] Add `NoReservedCollisions : TypeSpec → Prop`
  - forbids attr/shadow named `"state"`
- [x] Enforce it in `WFTypeSpec` (see §3)

### 1.3 Replay semantics unification
- [x] Replace Evolution’s `step` and `replayFromState` to be StreamId-based:
  - `step : IR → StreamId → State → Event → Option State`
  - applies reducer iff `inStream sid e`
- [x] Define `replayFromState` in terms of the same `step`
- [x] Update `Commutes` and `StepCommutes` to take `StreamId`, not `typeName`

Acceptance: the evolution proof uses the same event filtering semantics as `Core.Semantics.Replay.replay`.

---

## 2. Expr Typing v1 (Make typechecker match evaluator)

### 2.1 Fix `.get` typing (choose weak dynamic typing for v1)
v1 chooses a conservative rule:
- `.get e path` typechecks iff `e : tObj`
- result type is `tNull` (i.e., “may return null”), unless/until object schemas exist

- [ ] Fix `inferExprTyFuel` `.get` clause:
- [x] Fix `inferExprTyFuel` `.get` clause:
  - from “always none” to “if e : tObj then some tNull else none”
- [ ] Add corresponding declarative typing constructor in `HasType` (optional)
- [x] Ensure `.has` remains `Obj → Bool`

### 2.2 Row and state typing coherence
- [x] Introduce a dedicated VarRef for state-as-row OR type env entry:
  - Option 1: add `VarRef.rowState`
  - Option 2: treat `.row "state"` as valid with `tString` in `mkStateEnv`
- [x] Ensure evaluator exposes the same mechanism consistently in Commands/Replay/Constraints

### 2.3 Remove divergence between algorithmic and declarative typing
Pick one:
- [ ] (Preferred) Prove soundness for the fragment:
  - `inferExprTy Γ e = some t → HasType Γ e t`
  - for the supported constructors
- [x] Or delete `HasType` until it is used.

Acceptance: no supported Expr constructor is accepted by evaluator but rejected by the typechecker (and vice versa) on the v1 fragment.

---

## 3. WF(IR) v1 (Static Discipline)

Define WF predicates that mirror CICSC’s intended static constraints (not SQL).

### 3.1 WFTypeSpec
- [x] Add `WFTypeSpec : TypeSpec → Prop` in `Core/Meta/WF.lean` (new)
  - [x] `initialState ∈ states`
  - [x] `NoReservedCollisions ts`
  - [x] reducers only set state labels in `states` (if literal) OR accept dynamic state with constraint (choose one for v1)
  - [x] reducer ops refer only to declared attrs/shadows/reserved fields via typing env
  - [x] commands’ guards typecheck to Bool under env
  - [x] command emits payload expressions typecheck

### 3.2 WFIR
- [x] Add `WFIR : IR → Prop`
  - [x] all types satisfy WFTypeSpec
  - [x] constraints reference existing types
  - [x] views reference existing types (query semantics subset gated; see §6)

Acceptance: `checkIR` is either replaced by proofs about `WFIR`, or accompanied by lemmas connecting them.

---

## 4. Replay Properties v1

- [x] Prove replay determinism (definitional)
- [x] Prove replay preserves state well-formedness:
  - `WFTypeSpec ts → st0 WF → replayFromState ... WF`
- [x] Ensure initial state is well-formed:
  - `WFTypeSpec ts → WellFormedState ts (initialState ts)`

Acceptance: replay is total whenever the referenced type exists, and produces a well-formed state under WF assumptions.

---

## 5. Evolution v1 (Real Naturality)

v1 migration class is restricted to:
- eventType rename (or identity)
- optional drops
- state label rename
- no payload transforms
- no attr/shadow transforms

### 5.1 Migration WF strengthened
- [x] Fix coverage predicate naming:
  - `eventCoveredOrDropped` must reflect drop vs rename
- [x] Decide explicit-coverage vs identity-fallback; in v1 keep identity-fallback but require:
  - [ ] for every rename `tr`, target reducer exists in irTo
  - [ ] mapped target states exist in irTo

### 5.2 Proof obligations
- [ ] Prove `StepCommutes` for the restricted class without taking it as hypothesis
  - derive it from WFMigration + reducer compatibility conditions
- [ ] Prove `replay_commutes` using StreamId-based replay semantics
- [ ] Add an end-to-end example:
  - Ticketing v0→v1 migration commutes on all histories (not just sample)

Acceptance: naturality is a theorem with explicit assumptions, not an injected premise.

---

## 6. Query and bool_query Constraints v1 (Remove the stub)

v1 defines a minimal query semantics subset sufficient to support:
- filtering
- ordering
- limit/offset
- projection (no joins, no groupBy)

### 6.1 Implement QueryEval subset
- [ ] Add `Core/Semantics/QueryEval.lean` (new)
  - `evalQuery : IR → Query → List State → List State` (or over a SnapSet)
  - interpret Source.snap as “given rows” for v1 (external snapshot set passed in)

### 6.2 Use it in bool_query constraints
- [ ] Replace `evalQueryRowsCount` stub with:
  - `n := (evalQuery ...).length`
- [ ] Keep assertExpr restricted to rowsCount + args (if args exist)

Acceptance: bool_query constraints depend on actual query evaluation for the supported subset.

---

## 7. Examples v1

- [ ] Update Ticketing and Kanban examples to use `mkRow` and WF constraints
- [ ] Add one bool_query example that is nontrivial under QueryEval subset
- [ ] Add one migration proof that does not require `RestrictedMigrationClass` hypothesis (derives step commutation)

---

## 8. Acceptance Checklist

Lean Kernel v1 is complete when all are true:

- [ ] Evolution uses the same replay semantics as Core (StreamId filtering)
- [ ] Reducer env exposes `.row` and `"state"` consistently across all contexts
- [ ] Typechecker and evaluator agree on the v1 Expr fragment (including `.get`)
- [ ] WF(IR) predicates exist and are used as assumptions for theorems
- [ ] bool_query no longer uses the rowsCount stub; QueryEval subset exists
- [ ] Naturality theorem is proved without assuming `StepCommutes` as a hypothesis
- [ ] Ticketing v0→v1 migration proof does not rely on injected commutation premises
