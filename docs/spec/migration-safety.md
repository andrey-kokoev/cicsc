# CICSC Migration Safety (Scoped)

This document records the current migration-safety surface backed by Lean
theorems and executable tests.

## Formal Artifacts

Lean files:
- `lean/Cicsc/Evolution/Migration.lean`
- `lean/Cicsc/Evolution/Naturality.lean`

Representative theorems:
- `composeMigrations_assoc_of_compatible`
- `replay_commutes`
- `replay_commutes_restricted`

These are scope-bound by explicit premises in the theorem statements.

## Executable Evidence

Test suite:
- `tests/conformance/migration-composition.test.ts`

Covered scenarios:
- composition associativity (test model),
- inverse/roundtrip behavior for supported subset,
- unsafe-pattern detection and safety checklist behavior.

## Current Safety Contract

- Migration safety is currently a restricted contract tied to:
  - explicit compatibility assumptions,
  - restricted naturality premises,
  - supported reversible subset behavior.
- Unsupported patterns are not silently accepted; they are either rejected by
  checks/tests or remain out-of-scope.

## Operational Boundary

- This document does not yet define a full production rollback/cutover runbook.
- Build-time enforcement coverage beyond current test/model surface remains
  deferred.

