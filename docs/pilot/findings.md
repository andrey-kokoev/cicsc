# Pilot Findings Report

Date: 2026-02-12

## Executive Summary

Pilot hardening surfaced two active blockers:

- semantic regression in oracle replay/constraint verification tests
- dependency/runtime tooling gaps in local baseline execution

## Evidence Sources

- `docs/status/phase3-baseline.md`
- `docs/pilot/findings-classification.md`
- `scripts/phase3_baseline.sh`
- `scripts/phase3_ci_target.sh`

## Findings

1. Oracle replay + constraint test failures (`tests/oracle/replay-and-constraints.test.ts`).
- Severity: high
- Category: semantic bug
- Follow-up: roadmap section `T` item 1

2. Postgres adapter check requires explicit dependency bootstrap (`pg`).
- Severity: medium
- Category: ops/tooling gap
- Follow-up: roadmap section `T` item 2

3. Test runtime needed explicit `.ts` extension-resolution policy.
- Severity: medium
- Category: ops/tooling gap
- Follow-up: roadmap section `T` items 3-4

4. Adapter graph miswiring in sqlite lowering imports (fixed in this phase).
- Severity: medium
- Category: lowering gap
- Follow-up: monitor via baseline gate

## Forced Next Actions

- Complete roadmap section `T` before phase exit.
- Keep `./scripts/phase3_baseline.sh` as required pre-merge gate for Phase 3 work.
- Block pilot cutover until semantic regression is resolved.
