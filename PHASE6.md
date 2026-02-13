# PHASE6.md
## CICSC Phase 6: Field-Driven Concurrency Expansion

Phase 6 starts after Phase 5 closure and uses real vertical pressure to drive the
next semantic frontier: stronger concurrency guarantees, validated by deployment
evidence, then productization on top of proven behavior.

Execution sequence for Phase 6:
1. Field deployment expansion (6B)
2. Concurrency semantics hardening (6A), targeted by field findings
3. Productization/operability surface (6C), only for proven capability

---

## Phase Objective

Reach a state where:
- at least two verticals run through deploy/operate/evolve loops with measured outcomes,
- concurrency claims are upgraded from test-level confidence to explicit semantic contracts,
- operator tooling and SDK/CLI surfaces reflect only proven semantics.

---

## Milestone P6.1: Multi-Vertical Field Expansion (6B)

### Outcome
Expand from one reference vertical to a comparative field baseline.

### TODOs
- [x] P6.1.1 Select second reference vertical and freeze evaluation criteria artifact.
- [x] P6.1.2 Run staged workload for second vertical with the same invariant/conformance/migration gates.
- [x] P6.1.3 Add comparative incident register (ticketing vs second vertical) with severity and recurrence tags.
- [x] P6.1.4 Convert comparative findings into explicit roadmap checkboxes (no hidden backlog).
- [x] P6.1.5 Publish Phase 6 field baseline report with forced-next priorities only.

### Acceptance
- [x] Two verticals have reproducible staged-run evidence with artifacted outcomes.
- [x] Cross-vertical gaps are explicit and sequenced.

---

## Milestone P6.2: Concurrency Contract Hardening (6A)

### Outcome
Raise concurrency guarantees from implementation behavior to formalized contract.

### TODOs
- [x] P6.2.1 Define explicit supported concurrency model contract (stream-level + cross-stream boundaries).
- [x] P6.2.2 Add causality/partial-order replay conformance suite for declared model.
- [x] P6.2.3 Add deterministic conflict outcome matrix (abort/retry/merge) with proofs/tests per case.
- [x] P6.2.4 Add migration-under-concurrency drill covering pause/migrate/resume under concurrent load.
- [x] P6.2.5 Publish updated isolation/concurrency normative note with scoped exclusions.

### Acceptance
- [x] Concurrency claims are artifact-backed and test/proof linked.
- [x] Unsupported concurrent behaviors are rejected or explicitly documented as out of scope.

---

## Milestone P6.3: Proven-Surface Productization (6C)

### Outcome
Expose stable operational interfaces only for already-proven semantics.

### TODOs
- [ ] P6.3.1 Freeze CLI command contract for compile/install/migrate/verify/gates.
- [ ] P6.3.2 Add SDK contract tests for bundle lifecycle and tenant binding policies.
- [ ] P6.3.3 Add operator playbook for multi-tenant rollout, rollback, and incident triage.
- [ ] P6.3.4 Add policy control matrix (who can publish/bind/migrate) with executable checks.
- [ ] P6.3.5 Add “proven vs experimental” feature gating in docs and API surfaces.

### Acceptance
- [ ] Public operational surface is stable and mapped to proven backend semantics.
- [ ] No product-facing capability is exposed without conformance evidence.

---

## Milestone P6.4: Governance Gate for Phase 7

### Outcome
Prevent expansion without semantic closure.

### TODOs
- [ ] P6.4.1 Define objective Phase 6 exit checklist mapped to artifacts.
- [ ] P6.4.2 Require green dual-backend conformance + concurrency suites.
- [ ] P6.4.3 Require multi-vertical field report with unresolved criticals closed or explicitly deferred.
- [ ] P6.4.4 Add CI/doc checks rejecting phase/status drift for Phase 6 artifacts.
- [ ] P6.4.5 Mark Phase 7 blocked unless all checklist items are pass.

### Acceptance
- [ ] Phase transition is gated by objective artifacts, not subjective status claims.

---

## Exit Criteria (Phase 6)

- [ ] Two-vertical field validation is complete and reproducible.
- [ ] Concurrency model is explicit, tested, and normatively documented.
- [ ] Productized surfaces are limited to proven semantics.
- [ ] Governance checks enforce artifact-truth alignment continuously.
