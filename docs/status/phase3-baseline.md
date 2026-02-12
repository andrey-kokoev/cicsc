# Phase 3 Baseline (Stabilization Gate)

Date: 2026-02-12

Command:

`./scripts/phase3_baseline.sh`

Bootstrap prerequisite:

`./scripts/phase3_bootstrap.sh install`

## Result Snapshot

- `lean build`: PASS
- `dependency bootstrap check`: PASS
- `adapter sqlite typecheck`: PASS
- `adapter postgres typecheck`: PASS
- `phase3 CI target (oracle + lowering-shape + exec-smoke + typechecker negative)`: PASS

Summary: 5 passed, 0 failed.

## Verification Snapshot

Commands:

- `./scripts/phase3_bootstrap.sh check`
- `./scripts/phase3_baseline.sh`
- `./scripts/node_test.sh tests/conformance/sqlite-exec-vs-oracle.test.ts` (non-gating matrix)

Observed result:

- All baseline gates pass in current local environment.
- Full sqlite execution-vs-oracle matrix is partially failing (2 pass, 6 fail) and remains a tracked hardening backlog.

## Immediate Next Steps

1. Promote `scripts/phase3_ci_target.sh` as default validation entrypoint in automation.
2. Finalize deterministic `.ts` module resolution policy for runtime tests.
