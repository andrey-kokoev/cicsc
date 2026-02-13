# PHASE5.md
## CICSC Phase 5: Deployment-Grade Semantic Closure

Phase 5 converts the proof-backed substrate into a deployment-grade system with
strict conformance gates, safe migration operations, and usable Spec authoring.

---

## Phase Objective

Reach a state where:
- SQL backends are continuously checked against oracle semantics for supported operators,
- migration/cutover is executable with deterministic pass/fail checks,
- Spec DSL is human-usable while preserving Core IR correctness boundaries,
- multi-tenant bundle lifecycle and binding are operational,
- at least one real vertical validates the model under field pressure.

---

## Milestone P5.1: Full Conformance Gate Enforcement

### Outcome
Turn conformance from best-effort testing into hard CI entry criteria.

### TODOs
- [x] P5.1.1 Define required conformance suite matrix (sqlite + postgres where supported).
- [x] P5.1.2 Promote sqlite execution-vs-oracle matrix to required CI gate.
- [x] P5.1.3 Add differential coverage for join/group/having/subquery operators in supported scope (having deferred until Query AST support).
- [x] P5.1.4 Gate merges on conformance coverage report threshold and no untracked regressions.
- [x] P5.1.5 Add deterministic replay artifact retention policy for CI failures.

### Acceptance
- [ ] CI fails on any conformance regression in required matrix.
- [ ] Every newly lowered operator has SQL-vs-oracle differential coverage.

---

## Milestone P5.2: Migration Cutover and Rollback Protocol

### Outcome
Make migration safety operational (not only theorem/test level).

### TODOs
- [x] P5.2.1 Define executable migration preflight checklist (`SafeMigration` + runtime preconditions).
- [x] P5.2.2 Implement migration dry-run with replay verification report artifact.
- [x] P5.2.3 Implement cutover workflow with explicit pause/switch/resume boundaries.
- [x] P5.2.4 Implement rollback workflow for reversible subset with explicit failure handling.
- [x] P5.2.5 Add operator runbook and CLI commands for preflight/cutover/rollback.

### Acceptance
- [ ] Migration command surfaces deterministic pass/fail outcomes with structured reports.
- [ ] Reversible migrations can be rolled back under documented preconditions.

---

## Milestone P5.3: Spec DSL Ergonomics + Compiler Guarantees

### Outcome
Ship a user intent DSL that compiles to Core IR without leaking backend semantics.

### TODOs
- [x] P5.3.1 Freeze v1 Spec DSL grammar and desugaring contract.
- [x] P5.3.2 Add compiler diagnostics with path-qualified errors for all rejected constructs.
- [x] P5.3.3 Add negative compiler tests for invariant-weakening patterns.
- [x] P5.3.4 Add roundtrip fixtures (spec -> ir -> validated semantics artifacts).
- [x] P5.3.5 Add documentation and examples for non-programmer-authored workflows.

### Acceptance
- [ ] Spec author can express at least one full ticketing/CRM workflow without IR-shaped authoring.
- [ ] All DSL sugar compiles into fully typechecked Core IR with no semantic drift.

---

## Milestone P5.4: Bundle Registry + Tenant Binding

### Outcome
Operational multi-tenant lifecycle for versioned bundles.

### TODOs
- [x] P5.4.1 Implement bundle registry API/storage contract (publish, resolve, pin).
- [x] P5.4.2 Implement tenant -> bundle/version binding with immutable audit trail.
- [x] P5.4.3 Implement bundle signature/hash verification on install.
- [x] P5.4.4 Add lifecycle tests for publish/bind/upgrade/rollback.
- [x] P5.4.5 Add policy controls for who may bind or migrate tenant bundles.

### Acceptance
- [ ] Tenant binding is deterministic, auditable, and reproducible from bundle hashes.
- [ ] No runtime behavior depends on implicit or mutable bundle selection.

---

## Milestone P5.5: Postgres Adapter Semantic Parity

### Outcome
Bring Postgres to oracle-conformant status for declared supported subset.

### TODOs
- [x] P5.5.1 Define Postgres supported-scope contract mirroring sqlite scope model.
- [x] P5.5.2 Add postgres execution-vs-oracle differential matrix for in-scope operators.
- [x] P5.5.3 Add postgres constraint/reducer conformance checks where lowering exists.
- [x] P5.5.4 Align NULL/ordering/collation semantics policy and document deltas.
- [x] P5.5.5 Add cross-backend consistency gate (sqlite vs postgres vs oracle).

### Acceptance
- [ ] Postgres passes required differential conformance suite for declared scope.
- [ ] Any unsupported constructs are rejected at compile/typecheck time with explicit diagnostics.

---

## Milestone P5.6: Field Validation Vertical

### Outcome
Prove semantic fitness under real operational workload.

### TODOs
- [x] P5.6.1 Select one reference vertical and freeze its evaluation criteria.
- [x] P5.6.2 Run staged workload with invariants, conformance, and migration checks enabled.
- [x] P5.6.3 Collect drift/perf/missing-primitive incidents with severity labels.
- [x] P5.6.4 Convert findings into roadmap checkboxes (no hidden backlog).
- [x] P5.6.5 Publish phase report with forced-next priorities only.

### Acceptance
- [ ] At least one vertical run demonstrates deploy/operate/evolve loop with no invariant breaches.
- [ ] Remaining gaps are explicitly captured as sequenced roadmap items.

---

## Milestone P5.7: Governance Gate for Phase 6

### Outcome
Prevent phase transition without verified closure.

### TODOs
- [x] P5.7.1 Define objective Phase 5 exit checklist mapped to artifacts.
- [ ] P5.7.2 Require green required conformance gates for sqlite + postgres scoped matrices.
- [ ] P5.7.3 Require migration runbook and cutover/rollback drill evidence.
- [ ] P5.7.4 Require Spec DSL usability evidence from reference vertical.
- [ ] P5.7.5 Add CI/doc checks rejecting unchecked claims in phase/status docs.

### Acceptance
- [ ] Phase 6 cannot start unless all exit criteria artifacts are present and passing.

---

## Exit Criteria (Phase 5)

- [ ] Conformance gates are mandatory and broad enough to catch known regression classes.
- [ ] Migration operations are executable, reversible (where declared), and auditable.
- [ ] Spec DSL is ergonomically usable and compiles into invariant-safe Core IR.
- [ ] Bundle registry + tenant binding are operational and deterministic.
- [ ] Postgres parity is validated for declared scope.
- [ ] At least one real deployment cycle validates the system end-to-end.
