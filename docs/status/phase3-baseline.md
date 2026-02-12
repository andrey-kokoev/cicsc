# Phase 3 Baseline (Stabilization Gate)

Date: 2026-02-12

Command:

`./scripts/phase3_baseline.sh`

## Result Snapshot

- `lean build`: PASS
- `adapter sqlite typecheck`: PASS
- `adapter postgres typecheck`: FAIL
- `phase3 CI target (oracle + conformance + typechecker negative)`: FAIL

Summary: 2 passed, 2 failed.

## Failure Inventory

### 1) Postgres adapter typecheck

Command:

`npm --prefix adapters/postgres run check`

Observed failure:

- `Cannot find module 'pg' or its corresponding type declarations.`

Classification:

- Environment/dependency bootstrap issue (local runtime missing package install).

### 2) Phase 3 CI target semantic failures

Command:

`./scripts/phase3_ci_target.sh`

Observed failures:

- `tests/oracle/replay-and-constraints.test.ts` failing assertions.

Classification:

- Semantic/runtime mismatch requiring code-level fix.

## Immediate Next Steps

1. Resolve local dependency/bootstrap policy for adapter checks (`pg` install strategy in CI/local).
2. Fix oracle replay/constraint behavior regressions surfaced by CI target.
3. Re-run baseline and update this artifact.
