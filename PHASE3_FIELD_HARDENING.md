# PHASE3_FIELD_HARDENING.md
## CICSC Phase 3: Field Hardening

This phase executes post-v1.5 hardening before new research axes.

## 0. Phase Rules

- [x] 0.1 Add execution contract for one-checkbox/one-commit discipline.
- [x] 0.2 Add per-checkbox Definition of Done aligned with AGENTS and roadmap agreement.

### Execution Contract

- Exactly one checkbox is implemented per commit.
- No parallel checkbox execution.
- Each commit must include:
  - `Checkbox: <id>`
  - `Invariant: <strengthened property>`
  - `Proof/Test: <command/theorem/test target>`
  - `Docs: <paths changed>`
- A checkbox is not marked complete without verification evidence.
- If a checkbox is blocked, record blocker in this file and do not mark complete.

### Definition of Done (Per Checkbox)

A checkbox is complete only when all are true:

- Code or docs for that checkbox are implemented.
- Relevant typechecker/static guards are updated when semantics change.
- Required tests are added/updated:
  - oracle tests, and/or
  - SQL-vs-oracle conformance tests, and/or
  - typechecker negative tests, and/or
  - schema/runtime regression tests.
- No bundle-specific hacks are introduced.
- Behavior/semantic docs are updated when externally visible behavior changes.
- Verification evidence is present in commit message (`Proof/Test:` line).

## 1. Stabilization Gate (must pass before pilot)

- [x] 1.1 Add deterministic baseline script for build/test/typecheck/conformance.
- [x] 1.2 Eliminate known build graph inconsistencies blocking reliable CI signal.
- [x] 1.3 Add a single CI target running oracle tests + SQL conformance + typechecker negatives.
- [x] 1.4 Add baseline conformance artifact doc.

Baseline command: `./scripts/phase3_baseline.sh`

Current blocker inventory after 1.2:

- `adapter postgres typecheck`: external `pg` module not installed in local env.
- Node test execution on `.ts` files with extensionless relative imports requires runner/tooling alignment (address in 1.3 CI target).

CI target command: `./scripts/phase3_ci_target.sh`

Current 1.3 signal:

- Target runs with resolver alignment and currently reports semantic test failures in oracle replay assertions.

## 2. Conformance Hardening

- [x] 2.1 Add missing differential tests for lowering paths without oracle-vs-SQL coverage.
- [x] 2.2 Add typechecker negative tests for fail-fast semantic mismatches.
- [x] 2.3 Add replay determinism regression suite across representative histories/streams.
- [x] 2.4 Add constraint parity tests (oracle interpreter vs lowered backend).
- [x] 2.5 Add migration replay-verification regression suite for v1 migration class.

## 3. Pilot Deployment Preparation

- [x] 3.1 Select pilot vertical and record explicit scope contract.
- [x] 3.2 Define unsupported feature list for pilot (explicit rejections).
- [x] 3.3 Define tenant isolation and retention policy.
- [x] 3.4 Add pilot runbook (install/upgrade/rollback/verify-loop).
- [x] 3.5 Add structured pilot error taxonomy.

## 4. Pilot Execution (Validation-by-Usage)

- [x] 4.1 Stand up reproducible pilot environment.
- [x] 4.2 Execute scripted command/view/verify workload with invariant checks.
- [x] 4.3 Classify findings into semantic bug/typechecker gap/lowering gap/ops gap.
- [x] 4.4 Convert validated findings into roadmap checkboxes.
- [x] 4.5 Publish pilot findings report.

## 5. Productization Minimum (forced by pilot only)

- [x] 5.1 Add stable bundle registry protocol doc + reference contract.
- [x] 5.2 Add tenant->bundle binding lifecycle semantics (idempotent).
- [x] 5.3 Add migration/verification operator command set for cutovers.
- [x] 5.4 Add compatibility matrix: bundle x runtime x adapter.

## 6. Phase Exit and Freeze Decision

- [x] 6.1 Add objective Phase 3 exit checklist and pass/fail criteria.
- [ ] 6.2 Run full exit suite and publish evidence bundle.
- [ ] 6.3 Record decision commit: freeze core (v1.x) or open exactly one research axis.
