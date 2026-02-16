# Category Model for CICSC

This document defines the categorical structure that constrains CICSC’s design.
It is normative. Implementations must conform to it.

---

## 1. Objects

CICSC defines the following categories of objects:

- **Specᵥ**  
  User-facing intent specifications at version v.

- **IRᵥ**  
  Core semantic representations compiled from Specᵥ.

- **Historyᵥ**  
  Event histories conforming to IRᵥ.

- **Stateᵥ**  
  Reducible snapshots derived from Historyᵥ under IRᵥ.

These form object families indexed by version v ∈ ℕ.

---

## 2. Morphisms

The system defines the following total morphisms:

- **compileᵥ : Specᵥ → IRᵥ**  
  Compilation from user intent into core semantics.

- **lowerᵥ : IRᵥ → BackendSchemaᵥ**  
  Lowering from IR into backend-specific schema and query representations.

- **replayᵥ : Historyᵥ → Stateᵥ**  
  Deterministic fold of history into snapshot state.

- **executeᵥ : (Stateᵥ, Command) → Historyᵥ**  
  Command evaluation producing new events appended to Historyᵥ.

- **migrateᵥ→ᵥ₊₁ : (IRᵥ, Historyᵥ) → Historyᵥ₊₁**  
  Total history transformation induced by IR evolution.

All morphisms are required to be:
- total  
- deterministic  
- executable  

Partial or best-effort morphisms are forbidden.

---

## 3. Functors

The following functorial structure is enforced:

- **Compile : Spec → IR**  
  Mapping Spec objects and Spec-level rewrites to IR objects and IR-level rewrites.

- **Lower : IR → Backend**  
  Structure-preserving lowering into concrete storage/query categories.

- **Replay : History → State**  
  A fold functor from free event algebras to state algebras.

These functors must preserve composition and identity:
- Compile(id) = id  
- Lower(f ∘ g) = Lower(f) ∘ Lower(g)

---

## 4. Commutativity (Naturality Conditions)

All migrations must satisfy the following commuting diagram:

```
Historyᵥ  --migrateᵥ→ᵥ₊₁-->  Historyᵥ₊₁
   |                              |
 replayᵥ                        replayᵥ₊₁
   |                              |
 Stateᵥ   ----migrate_state---->  Stateᵥ₊₁
```

Where:

```
replayᵥ₊₁(migrateᵥ→ᵥ₊₁(h)) = migrate_state(replayᵥ(h))
```

This condition is enforced operationally via replay verification.

---

## 5. Invariants as Subobjects

Functional properties F(s) are treated as subobjects of Stateᵥ.
Migrations must preserve subobject membership:

```
s ∈ Fᵥ  ⇒  migrate_state(s) ∈ Fᵥ₊₁ ∪ ΔF
```

Constraint violations reject the morphism.

---

## 6. Constructive Invariance

All evolution steps must preserve future transformability:

- There must exist a migration path for any future Specᵥ₊₁.
- No evolution step may destroy the ability to define total morphisms in the future.

This forbids:
- in-place mutation of history
- irreversible schema changes
- non-replayable upgrades

---

## 7. Backend Conformance

For any backend lowering functor Lowerᵥ:

```
Replayᵥ(Historyᵥ) = OracleReplayᵥ(Historyᵥ)
                 = BackendReplayᵥ(Lowerᵥ(Historyᵥ))
```

This is enforced by differential testing between:
- the oracle interpreter
- the backend (SQLite, Postgres, etc.)

---

## 8. Design Constraints

The following are forbidden:

- runtime semantics not expressible in IR  
- backend-specific behavior not modeled in IR  
- migrations that are partial or non-deterministic  
- side channels that bypass history  
- constraints enforced outside replay or lowering semantics  

---

## 9. Consequences

From the above, CICSC guarantees:

- invariant-preserving evolution  
- backend-independent semantics  
- replay-verified migrations  
- compositional system design  
- auditability across versions  

---

## 10. Change Control

Any change that violates this model must:

- modify this document first, or
- be rejected.

This document constrains the system more strongly than any single implementation.

---

## 11. Collaboration Slice Category

The category **State/main** captures worktree collaboration:

- **Objects**: Morphisms `main → W` (worktrees branched from main)
- **Morphisms**: Integration paths `W₁ → W₂`

### 11.1 FF-Subcategory

**FF-State/main** is the full subcategory where all morphisms satisfy:

```
W₂ descends_from W₁  (FF-merge property)
```

### 11.2 Boundary Contraction

The integration functor:
```
integrate : State/main → Maybe(FF-State/main)
```

Is defined only when `W → main` is an FF-morphism. This **boundary contraction** ensures:

- Workers operate unconstrained in `State/main` (any branch)
- Integration enforces `FF-State/main` constraint
- Invalid structural states are unreachable by construction

### 11.3 Theorem (Unreachable Invalidity)

In **FF-State/main** with recency constraint `t`:
All reachable states satisfy structural invariants.

*Proof sketch*: By definition of FF-morphism, all worktrees descend from main. No merge conflicts possible. ∎

### 11.4 The Three-Phase Structure

Phase 1: **Dispatch** (Create Object)
- Creates new checkbox `c` with `A(c) = ⊥`
- No categorical constraint - just set expansion

Phase 2: **Claim** (Create Morphism)  
- Creates morphism `main → W` (branch creation)
- UNCONSTRAINED - workers can branch from anywhere

Phase 3: **Integrate** (Constrained Morphism)
- Creates morphism `W → main` via FF-merge
- FF-CONSTRAINED - must satisfy descent property

### 11.5 Axiomatic Bridge

The categorical model is connected to git execution via an axiomatic bridge:

```
git merge --ff-only worktree → main
```

Success yields evidence of `IsFFMorph` in the categorical model.
This is a **proof-carrying code** pattern:
1. Policy is formal (category model)
2. Execution checks compliance (git --ff-only)
3. Success yields proof object (IsFFMorph witness)

The proof obligation remains: prove git's `--ff-only` matches our `IsFFMorph` definition.

---

## 12. Change Control (Collaboration)

Changes to the collaboration layer must preserve:

1. FF-only integration (structural validity)
2. At-most-one assignment per checkbox (no double-assignment)
3. Evidence commit linkage (traceability)

This section is maintained in parallel with `lean/Cicsc/Evolution/FFIntegration.lean`.
