# Phase 3 Exit Evidence

Date: 2026-02-12

## Commands Executed

- `./scripts/phase3_baseline.sh`
- `./scripts/phase3_ci_target.sh`
- `node --loader ./tests/harness/ts-extension-loader.mjs --test tests/oracle/replay-determinism-multistream.test.ts`
- `node --loader ./tests/harness/ts-extension-loader.mjs --test tests/core/ir-type-reference-negative.test.ts`

## Results

- Baseline gate: PASS (5 pass, 0 fail)
- CI target: PASS (includes sqlite execution-vs-oracle smoke differential checks)
- Replay determinism regression: PASS
- Typechecker negative regression: PASS
- Extended sqlite execution-vs-oracle matrix: FAIL (2 pass, 6 fail; non-gating backlog)

## Exit Decision Input

Phase 3 stabilization checklist currently evaluates to **PASS**.
Extended backend execution parity remains incomplete and is tracked as post-exit hardening debt.

## Blocking Items

- `tests/conformance/sqlite-exec-vs-oracle.test.ts` parity gaps (join/direct source, arithmetic bool_query, expr matrix binds/operators)
