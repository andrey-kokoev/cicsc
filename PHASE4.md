# PHASE4.md
> Derived View: This file is a non-canonical execution view.
> Canonical status ledger: `control-plane/execution/execution-ledger.yaml`.
> Do not update checkbox truth here without matching `control-plane/execution/execution-ledger.yaml` update.

## CICSC Phase 4: Proof-Backed Field Reliability

Status: historical phase plan; remaining open items were closed or superseded by
executed Phase 5-8 governance/evidence artifacts.

Phase 4 turns current semantic scaffolding into production-grade, theorem-backed guarantees.
Focus: close objective gaps, not just execution-ledger checkboxes.

---

## Phase Objective

Reach a state where:
- declared semantics and runtime behavior are formally aligned for the supported feature surface,
- conformance failures are caught by default CI gates,
- migration and concurrency behavior are safe under explicit formal contracts,
- deployment guidance reflects true guarantees and explicit limits.

---

## Milestone P4.1: Truth Re-baseline

### Outcome
Reconcile documentation claims with proven behavior and current test signal.

### TODOs
- [x] P4.1.1 Audit `control-plane/execution/execution-ledger.yaml`, `LEAN_KERNEL_*`, `PHASE3_FIELD_HARDENING.md`, and status docs for claim drift.
- [x] P4.1.2 Introduce “Proved / Scoped / Deferred” status labels in normative docs.
- [x] P4.1.3 Add a single source-of-truth theorem index doc.
- [x] P4.1.4 Remove or reword any claim that exceeds proved scope.

### Acceptance
- [x] No normative doc claims stronger guarantees than theorem/test evidence supports.

---

## Milestone P4.2: Conformance Gate Hardening

### Outcome
Move from smoke parity toward broad operator-level execution parity.

### TODOs
- [x] P4.2.1 Keep current smoke + random differential tests as mandatory gate.
- [x] P4.2.2 Expand generated differential matrix to include join/group/having/subquery scenarios. (Superseded by Phase 7/8 scoped parity + explicit exclusions tracking.)
- [x] P4.2.3 Add deterministic seed replay artifact on test failure.
- [x] P4.2.4 Promote full sqlite execution-vs-oracle matrix from backlog to tracked closure plan. (Closed via Phase 7/8 required parity gates + risk mapping.)
- [x] P4.2.5 Add operator coverage report for conformance suites.

### Acceptance
- [x] CI fails on any regression in required conformance suites.
- [x] Coverage report shows gap areas explicitly.

---

## Milestone P4.3: Concurrency + Transaction Reliability

### Outcome
Make multi-user execution semantics explicit and testable.

### TODOs
- [x] P4.3.1 Connect `isCausal` with replay behavior via executable tests/theorems.
- [x] P4.3.2 Add transaction model tests for atomicity across multiple streams.
- [x] P4.3.3 Add write-write conflict tests and expected abort outcomes.
- [x] P4.3.4 Add deterministic replay tests under causally-equivalent history permutations.
- [x] P4.3.5 Document supported isolation guarantees and excluded scenarios.

### Acceptance
- [x] Concurrency claims in docs are backed by theorem or executable conformance tests.

---

## Milestone P4.4: Migration Safety Program

### Outcome
Establish migration operations that are safe, auditable, and replay-verified.

### TODOs
- [x] P4.4.1 Add migration composition test/proof suite (multi-step chains).
- [x] P4.4.2 Add reversible migration path tests for supported subset.
- [x] P4.4.3 Define and enforce `SafeMigration` checklist at build time.
- [x] P4.4.4 Add operator runbook for rollback/cutover with preconditions. (Closed in later migration protocol artifacts.)
- [x] P4.4.5 Add “unsafe pattern” detection and explicit rejection messaging.

### Acceptance
- [x] Migration workflows have deterministic pass/fail criteria.

---

## Milestone P4.5: Type Discipline Closure

### Outcome
Reduce runtime ambiguity by tightening static guarantees and documenting residual dynamic zones.

### TODOs
- [x] P4.5.1 Finalize typed fragment contract used by conformance and replay proofs. (Superseded by Lean kernel v1/v1.5 closure.)
- [x] P4.5.2 Add negative tests for every rejected expression/command pattern in scope. (Covered by later phase negative suites.)
- [x] P4.5.3 Add explicit runtime behavior notes for intentionally dynamic constructs. (Documented in feature-gate/spec notes in later phases.)
- [x] P4.5.4 Link checker outputs to structured operator diagnostics. (Implemented through phase gate artifact diagnostics.)

### Acceptance
- [x] Static rejection matrix is complete and maintained in CI.

---

## Milestone P4.6: Deployment-Proven Vertical

### Outcome
Validate semantics under real workflow pressure.

### TODOs
- [x] P4.6.1 Pick one vertical (ticketing/CRM/kanban) as Phase 4 reference deployment. (Superseded by multi-vertical Phase 5/6/8 evidence.)
- [x] P4.6.2 Run scripted workload with invariants + conformance checks enabled. (Closed by staged run artifacts in later phases.)
- [x] P4.6.3 Capture drift/missing-primitive/performance findings. (Closed by comparative incident artifacts in later phases.)
- [x] P4.6.4 Convert findings into concrete execution-ledger tasks with severity labels. (Closed by roadmap risk mapping artifacts.)
- [x] P4.6.5 Publish post-run report with “forced-next” items only. (Closed by phase reports and exit checklists.)

### Acceptance
- [x] At least one deployment report demonstrates semantic fit and remaining gaps.

---

## Milestone P4.7: Governance and Entry Criteria for Phase 5

### Outcome
Prevent premature phase transitions.

### TODOs
- [x] P4.7.1 Define objective Phase 4 exit checklist. (Superseded by later phase governance checklists.)
- [x] P4.7.2 Require green baseline + conformance + random differential suites. (Implemented via required-gates scripts in later phases.)
- [x] P4.7.3 Require doc truth audit pass. (Implemented via docs-consistency gate scripts.)
- [x] P4.7.4 Require unresolved critical gaps to be either closed or explicitly deferred with owner/date. (Implemented in critical register artifacts.)

### Acceptance
- [x] Phase 5 cannot start without checklist satisfaction.

---

## Exit Criteria (Phase 4)

- [x] Conformance and theorem claims are synchronized across code and docs.
- [x] SQL-vs-oracle execution parity gates are broad enough to catch known classes of regressions.
- [x] Concurrency and migration guarantees are operationally usable, not only conceptual.
- [x] At least one vertical deployment provides empirical validation and backlog forcing function.
- [x] Governance rules prevent unchecked claim inflation in future phases.

## Current Evidence

- `P4.1`: `docs/spec/truth-audit-v1.md`, `LEAN_KERNEL_V4.md` theorem index section.
- `P4.2`: `tests/conformance/random-oracle-harness.ts`,
  `tests/conformance/sqlite-random-vs-oracle.test.ts`,
  `tests/conformance/operator-coverage-report.ts`.
- `P4.3`: `tests/concurrency/causality-replay.test.ts`,
  `tests/concurrency/transaction-model.test.ts`,
  `docs/spec/isolation-guarantees.md`.
- `P4.4`: `tests/conformance/migration-composition.test.ts`.
