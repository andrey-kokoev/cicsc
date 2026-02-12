# Lean Formalization Plan for CICSC-Kernel (v0 Coherent Draft)

## 0. Scope Boundary

Formalize the **semantic kernel** only:

- Spec (core subset)
- Core IR
- Expr / Query / Reducer ops
- Replay semantics (history → state)
- Constraint semantics
- Migration semantics (history transform)
- Type system / typechecking judgments
- Proof obligations: determinism, commutation, preservation

Do not formalize:

- SQL engines, SQLite/D1, Postgres
- HTTP, Workers
- performance, scheduling
- real concurrency / networking

Backend conformance remains a **testable refinement** (oracle vs backend), not a proved theorem.

---

## 1. Repo Layout (Lean)

Use in-repo `lean/` directory.

Suggested layout:

- `lean/Cicsc/`
  - `Core/`
    - `Syntax.lean`          (inductive definitions: Expr, Query, ReducerOp, IR)
    - `Types.lean`           (typing domains, value types, schemas)
    - `Semantics/`
      - `ExprEval.lean`      (big-step eval for Expr)
      - `Replay.lean`        (fold of events to state)
      - `Constraints.lean`   (constraint satisfaction)
      - `Commands.lean`      (guard + emits, abstract execute relation)
    - `Meta/`
      - `Typecheck.lean`     (decidable checker + soundness theorems)
  - `Evolution/`
    - `Migration.lean`       (history transforms, totality)
    - `Naturality.lean`      (commuting diagram theorem)
  - `Examples/`
    - `Ticketing.lean`       (small IR instance)
    - `Kanban.lean`          (small IR instance)

---

## 2. Core Data Types (Lean Targets)

### 2.1 Values and Types
- `Val` as a tagged sum: `vBool | vInt | vString | vObj (List (String × Val)) | vNull | ...`
- `Ty` as a small universe: `tBool | tInt | tString | tObj | ...`

### 2.2 Expressions (core calculus)
Inductive `Expr` matching your tagged-object IR subset:
- literals
- variables (env refs)
- boolean algebra
- comparisons
- arithmetic
- `if`, `coalesce`
- `get` over objects
- (optional) `map_enum`

### 2.3 Events and History
- `Event := { tenantId, entityType, entityId, seq, eventType, payload, ts, actor }`
- `History := List Event`

### 2.4 State / Snapshot
- `State := { st : String, attrs : List (String × Val), shadows : List (String × Val) }`

### 2.5 Reducer
- `ReducerOp := SetState Expr | SetAttr String Expr | SetShadow String Expr | ...`
- `applyOp : Env → State → ReducerOp → State`
- `applyReducer : IR → State → Event → State` (dispatch by event_type)

### 2.6 IR
- `IR := { version : Nat, types : List (String × TypeSpec), constraints, views }`
- `TypeSpec := { states : List String, initialState : String, reducer : List (EventType × List ReducerOp), ... }`

---

## 3. Semantics (Definitions)

### 3.1 Expression Evaluation
Define total big-step evaluator:
- `eval : Env → Expr → Val`

Prove:
- determinism: `eval env e = v` is unique (definitional if using `def eval`)

### 3.2 Replay
Define:
- `replay : IR → TypeName → History → Option State`
as:
- start from `initState`
- apply reducer for each event (typed by entity stream)
- return `none` when type lookup fails

Prove:
- totality under type-existence premise (`lookupTypeSpec ir typeName = some ts`)

### 3.3 Constraints
Define:
- `Constraint := State → Prop` for snapshot constraints
- `satisfies : List Constraint → State → Prop`

For bool_query constraints:
- model as `History/State → Prop` via abstract `QueryEval`
- or treat as constraints over a snapshot-set `SnapSet` (finite list)

---

## 4. Proof Targets (First Milestone)

### Theorem A — Replay Totality Under Lookup
Meaningful v0 statement:
- if type exists in IR, `replay` returns `some st`.

### Theorem B — Type Safety (No Illegal Field Access)
Define a typing judgment:
- `Γ ⊢ e : τ`

Prove:
- If `Γ ⊢ e : τ` and `env : Γ` then `eval env e` does not get stuck.

(Lean version: evaluation is total; prove it respects typing: `eval env e` has type τ.)

### Theorem C — Reducer WF Preservation
If reducer preservation assumption holds, then one-step reducer application preserves:
- state label in allowed states

### Theorem D — Constraint Preservation Under Replay
For v0 snapshot constraints only, show:
- snapshot constraints are decidable
- snapshot constraints depend only on replay result (extensionality)

Bool-query status in v0:
- query evaluation is currently a placeholder (`rows.length`-based)
- no theorem should claim full bool-query semantic adequacy until `Query` semantics are formalized

---

## 5. Migration Formalization (Evolution Milestone)

Define:
- `migrateEvent : MigrationSpec → Event → Option Event`
- `migrateHist : History → History`
- `migrateState : State → State`

Current v0 migration contract:
- total-by-identity fallback for unknown event transforms
- `none` means explicit drop only

Well-formedness predicate:
- `WFMigration ms irFrom irTo`
- non-dropped target reducer existence in `irTo`
- `stateMap` target state validity in `irTo`

### Theorem E — Naturality / Commutation
Prove (history induction):
- `replay_commutes : WFMigration ... → (typeName = ms.entityType) → StepCommutes ... → ∀ h s0, Commutes ... s0 h`

This is the categorical tightness core.

Approach:
- define step-level commutation lemma (`StepCommutes`)
- lift to replay commutation by `History` induction (`foldl` pattern)

---

## 6. Practical Strategy

### 6.1 Start with the smallest core
- only snapshot constraints
- no joins, no group_by
- minimal Expr operators

### 6.2 Add features by proof obligation
For each new Expr/Query feature:
- add typing rule
- add eval clause
- extend soundness theorem

### 6.3 Keep the kernel executable
Prefer `def` over `axiom` where possible:
- makes proofs easier
- allows “proof by computation” for examples

---

## 7. Initial Deliverables (Concrete)

- `Cicsc/Core/Syntax.lean`
- `Cicsc/Core/Semantics/ExprEval.lean`
- `Cicsc/Core/Semantics/Replay.lean`
- `Cicsc/Core/Meta/Typecheck.lean` (decidable checker subset)
- `Cicsc/Evolution/Naturality.lean` (commutation proof for simple migrations)
- `Cicsc/Examples/Ticketing.lean` (instantiate IR + run replay)

---

## 8. Acceptance Criteria for “Lean Kernel v0”

- `replay` definitional and total under type lookup premise
- type soundness theorem for Expr subset
- reducer preserves well-formedness
- commutation theorem for a non-trivial migration example
- example vertical compiles and proofs check with `lake build`

---

## 9. Current Status Note (as of v0 roadmap completion)

Implemented in repository:
- Core syntax/types/semantics modules exist and are wired from `lean/Cicsc.lean`
- replay totality-under-lookup theorem exists
- evolution modules define `WFMigration`, `StepCommutes`, and `replay_commutes`
- non-identity Ticketing migration example (event rename + state rename) exists

Known deliberate limits:
- query formalization is represented through constraints module; no separate `QueryEval.lean` yet
- migration/state transforms currently model renaming/drop-style evolution, not full payload/schema rewrites
