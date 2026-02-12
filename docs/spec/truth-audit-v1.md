# CICSC Phase 4 Truth Audit (v1)

Date: 2026-02-12
Scope: Evidence-backed status for current `main`.

This is a status index, not a new semantics source. It tracks:
- proved (Lean theorem in repo),
- scoped (proved for an explicitly restricted fragment),
- tested (executable TS test coverage),
- deferred (not yet established).

## Conformance

- `Scoped/Proved`: `execSQL_lowerQuery_conforms_execShape` in `lean/Cicsc/Sql/Conformance.lean`.
- `Scoped boundary`: out-of-scope operators in `lean/Cicsc/Core/Semantics/ConformanceScope.lean`:
  - `outOfScopeQueryOpForExecTheorem`
  - `outOfScopeExprForExecTheorem`
- `Tested`: `tests/conformance/sqlite-random-vs-oracle.test.ts`,
  `tests/conformance/sqlite-exec-vs-oracle-smoke.test.ts`,
  `tests/conformance/operator-coverage-report.ts`.

Status: `Scoped + Tested`.

## Replay, Causality, Isolation

- `Proved`: replay/causality theorems in `lean/Cicsc/Core/Semantics/CausalityReplay.lean`,
  including `replay_deterministic_on_causallyEquivalent_streams`.
- `Proved`: snapshot/conflict theorems in `lean/Cicsc/Core/Semantics/Isolation.lean`,
  including `snapshot_no_dirty_reads` and `writeWrite_conflict_abort_or_serialize`.
- `Tested`: `tests/concurrency/causality-replay.test.ts`,
  `tests/concurrency/transaction-model.test.ts`.

Status: `Proved + Tested` (with explicit theorem scopes).

## Migration Algebra/Safety

- `Proved`: `composeMigrations_assoc_of_compatible` in `lean/Cicsc/Evolution/Migration.lean`.
- `Proved`: naturality/commutation in `lean/Cicsc/Evolution/Naturality.lean`
  (`replay_commutes`, `replay_commutes_restricted`).
- `Tested`: composition/inverse/safety scenarios in
  `tests/conformance/migration-composition.test.ts`.

Status: `Proved + Tested` (subset-scoped where stated in theorem premises).

## Type Discipline

- `Proved`: fragment theorems in `lean/Cicsc/Core/Meta/Typecheck.lean`:
  - `inferExprTy_sound_v4_fragment`
  - `inferExprTy_complete_up_to_subsumption_v4`
  - `inferExprTy_principal_v4`
- `Scoped`: fragment predicates `TypingV4Fragment` / `supportsTypingV4Expr`.
- `Doc`: fragment surface in `docs/spec/typing-v4-fragment.md`.

Status: `Proved + Scoped`.

## Deferred Items

- Full, unrestricted SQL conformance theorem (beyond current v4 executable subset).
- Production isolation guarantees documentation aligned 1:1 with backend behavior.
- Migration operator runbook and formal cutover/rollback operational contract.
- Phase 4 deployment vertical validation (`P4.6`).

