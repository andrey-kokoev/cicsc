# Pilot Findings Classification

## Classification Buckets

- semantic bug
- typechecker gap
- lowering gap
- ops/tooling gap

## Current Classified Findings

1. `tests/oracle/replay-and-constraints.test.ts` failing assertions.
- Bucket: semantic bug
- Why: runtime/oracle behavior mismatch, not just harness failure.
- Status: resolved and promoted into CI gate.

2. `npm --prefix adapters/postgres run check` cannot resolve `pg` in local baseline.
- Bucket: ops/tooling gap
- Why: dependency/bootstrap policy gap for deterministic local and CI checks.
- Status: resolved by `scripts/phase3_bootstrap.sh`.

3. Node `.ts` extensionless import execution needed explicit loader for stable test target.
- Bucket: ops/tooling gap
- Why: test runner resolution mismatch; addressed by `tests/harness/ts-extension-loader.mjs`.

4. Broken adapter-to-core import edges in sqlite adapter (`../../../core/...` pathing).
- Bucket: lowering gap
- Why: lowering package dependency graph was miswired.

5. Full sqlite execution-vs-oracle matrix still has parity failures (`tests/conformance/sqlite-exec-vs-oracle.test.ts`).
- Bucket: lowering gap
- Why: remaining SQL execution parity mismatches (query shape/expr binds/arithmetic branch behavior).
- Status: open; CI gate currently enforces smoke parity via `tests/conformance/sqlite-exec-vs-oracle-smoke.test.ts`.
