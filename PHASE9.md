# PHASE9.md
> Derived View: This file is a non-canonical execution view.
> Canonical status ledger: `control-plane/execution/execution-ledger.yaml`.
> Do not update checkbox truth here without matching `control-plane/execution/execution-ledger.yaml` update.

## CICSC Phase 9: Capability Expansion Under Guarded Equivalence

Phase 9 starts after Phase 8 closure and focuses on expanding capability surface
without relaxing proven invariants, equivalence discipline, or migration safety.

Execution sequence for Phase 9:
1. SQL capability expansion with oracle-backed conformance
2. Cross-backend parity hardening (SQLite/Postgres)
3. Migration and operations hardening for expanded surface
4. Field deployment validation and governance gate for next phase

---

## Phase Objective

Reach a state where:
- deferred SQL capability gaps are either implemented with differential coverage or explicitly retained as blocked,
- SQLite and Postgres behavior remain equivalent to oracle semantics on the declared supported surface,
- migrations on expanded features remain replay-verified and operationally deterministic,
- deployment evidence drives execution-ledger forcing functions,
- phase progression remains artifact-gated.

---

## Milestone P9.1: SQL Capability Expansion With Conformance

### Outcome
Close highest-value deferred SQL surface gaps using fail-fast typing and oracle differential tests.

### TODOs
- [x] P9.1.1 Freeze Phase 9 SQL scope matrix (supported/deferred operators and query forms).
- [x] P9.1.2 Implement selected deferred query lowering candidates (e.g., `HAVING`, `EXISTS`) behind explicit gates.
- [x] P9.1.3 Add SQL execution-vs-oracle differential suites for each newly enabled construct.
- [x] P9.1.4 Add negative typecheck coverage for unsupported forms to enforce compile-time rejection.
- [x] P9.1.5 Publish SQL-surface closure report with residual exclusions and risk labels.

### Acceptance
- [x] Every newly enabled SQL construct has executable oracle differential coverage.
- [x] Unsupported constructs fail fast at compile time with path-qualified diagnostics.

---

## Milestone P9.2: Cross-Backend Parity Hardening (SQLite + Postgres)

### Outcome
Treat backend parity as a required gate for the expanded SQL and runtime surface.

### TODOs
- [x] P9.2.1 Freeze backend parity contract for Phase 9 (semantic classes + scale envelope).
- [x] P9.2.2 Add deterministic cross-backend edge-case suites (null/collation/numeric/time behavior).
- [x] P9.2.3 Add seeded random differential sweeps for SQLite/Postgres/oracle over expanded operators.
- [x] P9.2.4 Add parity triage artifact with regression class labeling and owner assignment.
- [x] P9.2.5 Publish backend parity report and required-gates policy update.

### Acceptance
- [x] Expanded backend surface remains parity-verified under declared envelope.
- [x] Any non-equivalence is either fixed or explicitly deferred with owner/date.

---

## Milestone P9.3: Migration + Operational Reliability on Expanded Surface

### Outcome
Ensure new capability surface does not compromise migration determinism, rollback safety, or tenant isolation.

### TODOs
- [x] P9.3.1 Extend migration protocol contract for newly supported SQL/query constructs.
- [x] P9.3.2 Add migration drill suites covering upgraded features (preflight/dry-run/cutover/rollback).
- [x] P9.3.3 Add post-cutover execution-vs-oracle differential checks on migrated streams.
- [x] P9.3.4 Add updated SLO/error-budget gates for verify/migrate/command paths under expanded load.
- [x] P9.3.5 Publish migration safety and operations report with unresolved criticals disposition.

### Acceptance
- [x] Expanded-surface migrations remain replay-verified and deterministic.
- [x] Operational gates detect and block regression before phase promotion.

---

## Milestone P9.4: Deployment Validation and Governance Gate for Phase 10

### Outcome
Validate expanded surface under real workflow pressure and enforce objective exit control.

### TODOs
- [x] P9.4.1 Select and freeze Phase 9 reference deployment set (at least two verticals).
- [x] P9.4.2 Run scripted workloads with invariants + parity + migration gates enabled.
- [x] P9.4.3 Capture drift/missing-primitive/performance findings with severity labels.
- [x] P9.4.4 Convert findings into forced-next execution-ledger tasks (no speculative backlog inflation).
- [x] P9.4.5 Define and enforce objective Phase 9 exit checklist + Phase 10 block gate.

### Acceptance
- [x] Deployment evidence confirms semantic fit of expanded surface.
- [x] Phase transition remains artifact-truth-governed, not narrative.

---

## Exit Criteria (Phase 9)

- [x] Deferred SQL capability items are either closed with conformance evidence or explicitly deferred.
- [x] SQLite/Postgres parity is maintained for the declared expanded feature envelope.
- [x] Migration and operational guarantees remain deterministic and auditable after expansion.
- [x] Deployment findings are converted into forced-next execution-ledger tasks with ownership.
- [x] Governance checks continuously enforce code/doc/artifact consistency.
