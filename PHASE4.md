# PHASE4.md
## CICSC Phase 4: Proof-Backed Field Reliability

Phase 4 turns current semantic scaffolding into production-grade, theorem-backed guarantees.
Focus: close objective gaps, not just roadmap checkboxes.

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
- [x] P4.1.1 Audit `ROADMAP.md`, `LEAN_KERNEL_*`, `PHASE3_FIELD_HARDENING.md`, and status docs for claim drift.
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
- [ ] P4.2.2 Expand generated differential matrix to include join/group/having/subquery scenarios.
- [x] P4.2.3 Add deterministic seed replay artifact on test failure.
- [ ] P4.2.4 Promote full sqlite execution-vs-oracle matrix from backlog to tracked closure plan.
- [x] P4.2.5 Add operator coverage report for conformance suites.

### Acceptance
- [ ] CI fails on any regression in required conformance suites.
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
- [ ] P4.3.5 Document supported isolation guarantees and excluded scenarios.

### Acceptance
- [ ] Concurrency claims in docs are backed by theorem or executable conformance tests.

---

## Milestone P4.4: Migration Safety Program

### Outcome
Establish migration operations that are safe, auditable, and replay-verified.

### TODOs
- [x] P4.4.1 Add migration composition test/proof suite (multi-step chains).
- [x] P4.4.2 Add reversible migration path tests for supported subset.
- [x] P4.4.3 Define and enforce `SafeMigration` checklist at build time.
- [ ] P4.4.4 Add operator runbook for rollback/cutover with preconditions.
- [x] P4.4.5 Add “unsafe pattern” detection and explicit rejection messaging.

### Acceptance
- [ ] Migration workflows have deterministic pass/fail criteria.

---

## Milestone P4.5: Type Discipline Closure

### Outcome
Reduce runtime ambiguity by tightening static guarantees and documenting residual dynamic zones.

### TODOs
- [ ] P4.5.1 Finalize typed fragment contract used by conformance and replay proofs.
- [ ] P4.5.2 Add negative tests for every rejected expression/command pattern in scope.
- [ ] P4.5.3 Add explicit runtime behavior notes for intentionally dynamic constructs.
- [ ] P4.5.4 Link checker outputs to structured operator diagnostics.

### Acceptance
- [ ] Static rejection matrix is complete and maintained in CI.

---

## Milestone P4.6: Deployment-Proven Vertical

### Outcome
Validate semantics under real workflow pressure.

### TODOs
- [ ] P4.6.1 Pick one vertical (ticketing/CRM/kanban) as Phase 4 reference deployment.
- [ ] P4.6.2 Run scripted workload with invariants + conformance checks enabled.
- [ ] P4.6.3 Capture drift/missing-primitive/performance findings.
- [ ] P4.6.4 Convert findings into concrete roadmap tasks with severity labels.
- [ ] P4.6.5 Publish post-run report with “forced-next” items only.

### Acceptance
- [ ] At least one deployment report demonstrates semantic fit and remaining gaps.

---

## Milestone P4.7: Governance and Entry Criteria for Phase 5

### Outcome
Prevent premature phase transitions.

### TODOs
- [ ] P4.7.1 Define objective Phase 4 exit checklist.
- [ ] P4.7.2 Require green baseline + conformance + random differential suites.
- [ ] P4.7.3 Require doc truth audit pass.
- [ ] P4.7.4 Require unresolved critical gaps to be either closed or explicitly deferred with owner/date.

### Acceptance
- [ ] Phase 5 cannot start without checklist satisfaction.

---

## Exit Criteria (Phase 4)

- [ ] Conformance and theorem claims are synchronized across code and docs.
- [ ] SQL-vs-oracle execution parity gates are broad enough to catch known classes of regressions.
- [ ] Concurrency and migration guarantees are operationally usable, not only conceptual.
- [ ] At least one vertical deployment provides empirical validation and backlog forcing function.
- [ ] Governance rules prevent unchecked claim inflation in future phases.

## Current Evidence

- `P4.1`: `docs/spec/truth-audit-v1.md`, `LEAN_KERNEL_V4.md` theorem index section.
- `P4.2`: `tests/conformance/random-oracle-harness.ts`,
  `tests/conformance/sqlite-random-vs-oracle.test.ts`,
  `tests/conformance/operator-coverage-report.ts`.
- `P4.3`: `tests/concurrency/causality-replay.test.ts`,
  `tests/concurrency/transaction-model.test.ts`.
- `P4.4`: `tests/conformance/migration-composition.test.ts`.
