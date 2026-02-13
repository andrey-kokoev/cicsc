# Lean Kernel v1 -> v1.5 Migration Guide

## Scope

This guide documents update steps for contributors moving proofs/examples from
Lean kernel v1 to v1.5 coherency-complete surfaces.

## Required API updates

1. Constraint evaluator naming
- Old: `holdsConstraintV0`
- New canonical: `holdsConstraint`
- Snapshot-only helper: `holdsSnapshotConstraintOnly`

2. Replay well-formedness theorem assumptions
- Old pattern: replay theorems requiring external `ReducerPreservesWF`
- New pattern: replay theorems require `WFTypeSpec` (closure proved internally)

3. Typing bridge usage
- Prefer theorem bridge from algorithmic inference to declarative typing:
  `inferExprTy_sound`, `inferExprTyFuel_sound_atSize`.

## Non-breaking semantics notes

- `evalExpr`, `evalQuery`, and `applyReducer` runtime semantics are unchanged.
- v1.5 primarily closes coherency/proof/documentation gaps.

## Validation

Run:

```bash
cd lean
lake build
```

Expected result: clean build including examples.
