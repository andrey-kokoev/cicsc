# CICSC Isolation Guarantees (Scoped)

This document states the current, evidence-backed isolation surface.

## Formal Artifacts

Lean file:
- `lean/Cicsc/Core/Semantics/Isolation.lean`

Key theorems currently available:
- `snapshot_no_dirty_reads`
- `writeWrite_conflict_abort_or_serialize`

These theorems are the authoritative formal basis for current claims.

## Executable Evidence

Test suites:
- `tests/concurrency/transaction-model.test.ts`
- `tests/concurrency/causality-replay.test.ts`

Current tested scenarios include:
- per-stream sequence isolation behavior,
- write-write conflict abort behavior in the test executor model,
- causal ordering/replay determinism checks.

## Current Guarantee Scope

- Snapshot/read consistency is claimed only within the formal model and theorem
  premises in `Isolation.lean`.
- Conflict behavior is claimed only as expressed by
  `writeWrite_conflict_abort_or_serialize`.
- Cross-backend operational isolation behavior is not fully specified here and
  remains an implementation-level responsibility.

## Explicit Non-Claims

- This document does not claim full serializability.
- This document does not claim distributed transaction semantics.
- This document does not define backend-specific lock-manager behavior.

