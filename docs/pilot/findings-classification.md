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

2. `npm --prefix adapters/postgres run check` cannot resolve `pg` in local baseline.
- Bucket: ops/tooling gap
- Why: dependency/bootstrap policy gap for deterministic local and CI checks.

3. Node `.ts` extensionless import execution needed explicit loader for stable test target.
- Bucket: ops/tooling gap
- Why: test runner resolution mismatch; addressed by `tests/harness/ts-extension-loader.mjs`.

4. Broken adapter-to-core import edges in sqlite adapter (`../../../core/...` pathing).
- Bucket: lowering gap
- Why: lowering package dependency graph was miswired.
