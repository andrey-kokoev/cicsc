# CICSC Type Discipline (v4 Scoped)

This document records the current typed fragment and proof surface used by the
Lean v4 kernel artifacts.

It does not extend semantics; it summarizes current scope.

## Fragment Boundary

Canonical fragment definition lives in:
- `lean/Cicsc/Core/Meta/Typecheck.lean`
  - `supportsTypingV4Expr`
  - `TypingV4Fragment`

Human-readable surface summary:
- `docs/spec/typing-v4-fragment.md`

Current explicit exclusion:
- `call(fn, args)`

## Core Theorems (Scoped)

In `lean/Cicsc/Core/Meta/Typecheck.lean`:
- `inferExprTy_sound_v4_fragment`
- `inferExprTy_complete_up_to_subsumption_v4`
- `inferExprTy_principal_v4`

These are scoped to the declared v4 fragment and their explicit premises.

## Supporting Definitions

In `lean/Cicsc/Core/Meta/Typecheck.lean`:
- `subsumes`
- `HasTypeAlg`

These define the completeness-up-to-subsumption and algorithmic typing bridge
used by v4 acceptance criteria.

## Known Limits

- This scope is not a full-language completeness claim.
- Constructs outside `TypingV4Fragment` are intentionally excluded from v4
  theorem commitments.
- Dynamic runtime behaviors outside the fragment are tracked as deferred work.

## Evidence Pointers

- Plan/closure mapping: `LEAN_KERNEL_V4.md`
