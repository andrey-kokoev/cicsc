# Pilot Findings Report

Date: 2026-02-12

## Executive Summary

Pilot hardening resolved bootstrap/CI determinism and surfaced remaining execution-parity gaps:

- sqlite execution-vs-oracle full matrix has 6 failing cases (2 passing)

## Evidence Sources

- `docs/status/phase3-baseline.md`
- `docs/pilot/findings-classification.md`
- `scripts/phase3_baseline.sh`
- `scripts/phase3_ci_target.sh`

## Findings

1. Oracle replay + constraint test failures (`tests/oracle/replay-and-constraints.test.ts`).
- Status: resolved
- Follow-up: covered in gating CI target.

2. Postgres adapter check requires explicit dependency bootstrap (`pg`).
- Status: resolved
- Follow-up: enforced by `./scripts/phase3_bootstrap.sh check`.

3. Full sqlite execution-vs-oracle matrix is not yet green (`tests/conformance/sqlite-exec-vs-oracle.test.ts`).
- Severity: medium
- Category: lowering gap
- Follow-up: keep smoke differential test in CI and close remaining matrix failures incrementally.

4. Adapter graph miswiring in sqlite lowering imports (fixed in this phase).
- Severity: medium
- Category: lowering gap
- Follow-up: monitor via baseline gate

## Forced Next Actions

- Complete roadmap section `T` before phase exit.
- Keep `./scripts/phase3_baseline.sh` as required pre-merge gate for Phase 3 work.
- Keep `tests/conformance/sqlite-exec-vs-oracle-smoke.test.ts` as required SQL execution parity gate.
