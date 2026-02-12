# Phase 3 Exit Evidence

Date: 2026-02-12

## Commands Executed

- `./scripts/phase3_baseline.sh`
- `./scripts/phase3_ci_target.sh`
- `node --loader ./tests/harness/ts-extension-loader.mjs --test tests/oracle/replay-determinism-multistream.test.ts`
- `node --loader ./tests/harness/ts-extension-loader.mjs --test tests/core/ir-type-reference-negative.test.ts`

## Results

- Baseline gate: FAIL (2 pass, 2 fail)
- CI target: FAIL (`tests/oracle/replay-and-constraints.test.ts` assertions)
- Replay determinism regression: PASS
- Typechecker negative regression: PASS

## Exit Decision Input

Phase 3 exit checklist currently evaluates to **FAIL** due unresolved high-severity semantic regression and adapter dependency/bootstrap gap.

## Blocking Items

- `ROADMAP.md` section `T` item 1 (oracle replay + constraint regression)
- `ROADMAP.md` section `T` item 2 (dependency/bootstrap policy)
