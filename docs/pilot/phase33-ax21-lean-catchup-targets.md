# Phase 33 Lean/Kernel Catch-up Targets

This document defines the formalization targets required to support the expanded objective claims established in Phase 32 (Era 2).

## 1. Concurrency (OBJ1)
- **Target**: Extend `Semantics/Replay.lean` to support concurrent history linearization proofs.
- **Requirement**: Prove that the deterministic conflict outcome matrix (abort/retry/merge) is sound under the abstract machine model.
- **Claim Support**: Validates the "expanded concurrency envelope" artifacts.

## 2. Drift and Side-Effects (OBJ2)
- **Target**: Formally define the "drift boundary" between the immutable oracle trace and side-effecting command executions.
- **Requirement**: Define a refined `WFGovernance` predicate that constrains state divergence.
- **Claim Support**: Provides the formal basis for "drift-budget governance" artifacts.

## 3. Desugaring Invariants (OBJ3)
- **Target**: Implement formal verification for Spec -> Core IR desugaring in `Meta/Typecheck.lean`.
- **Requirement**: Prove that every Spec construct maps to a well-typed Core IR expression.
- **Claim Support**: Ensures usability improvements in "usability-envelope" do not introduce hidden semantic drift.

## 4. Multi-Version Schema Evolution (OBJ4)
- **Target**: Formalize the state transformation mapping for joined and grouped sources in `Evolution/Migration.lean`.
- **Requirement**: Prove that `replay_commutes` holds for migrations involving schema joins and attribute moves.
- **Claim Support**: Supports the "expanded migration-envelope" repeatability claims.

## 5. Operator Parity Closure (OBJ5)
- **Target**: Add final abstract semantics for `HAVING` and `EXISTS` to the core calculus.
- **Requirement**: Align the Lean oracle with the "expanded parity-envelope" backend baseline.
- **Claim Support**: Completes the semantic definition for Phase 32 forced-next operators.

---
This document closes `AX2.1`.
