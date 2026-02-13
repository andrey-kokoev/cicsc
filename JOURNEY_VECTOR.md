# JOURNEY_VECTOR.md
## CICSC Journey Vector (Canonical)

This document is the single canonical view of:
- mission objectives,
- current position,
- completed vs open phase trajectory,
- artifact-backed gates,
- forced-next sequence.

It is a navigation index, not a replacement for phase or theorem documents.

---

## 1. North Star Objectives

From `AGENTS.md`, CICSC success is:
- invariants hold under concurrency,
- IR and runtime semantics are aligned and enforced,
- Spec DSL is usable by humans,
- migrations are executable and replay-verified,
- SQLite/D1 and Postgres are semantically equivalent to oracle for declared scope.

---

## 2. Current Position

Current state on `main`:
- Lean kernel status: v4 scoped closure complete (`LEAN_KERNEL_V4.md`).
- Phase status: Phase 10 complete (`PHASE10.md` all checked).
- Roadmap status: `AA` section complete (`ROADMAP.md`).
- Governance status: Phase 10 closure + Phase 11 gate are artifact-driven
  (`docs/pilot/phase10-closure-report.json`, `docs/pilot/phase11-gate.json`).

---

## 3. Journey Timeline

1. Foundation and runtime hardening: complete.
2. Lean coherency closure and scoped formal expansion: complete through v4.
3. Field hardening and pilot evidence loops: complete through Phase 10.
4. Forced-next closure and production continuity governance: complete through Phase 10.
5. Next vector: Phase 11 planning/execution under the same gate discipline.

---

## 4. Objective-to-Evidence Map

- Invariants under concurrency:
  - `docs/spec/isolation-guarantees.md`
  - `docs/pilot/phase7-concurrency-adversarial.json`
  - `docs/pilot/phase8-chaos-drills.json`
  - `tests/concurrency/transaction-model.test.ts`
  - `tests/concurrency/causality-replay.test.ts`

- IR/runtime semantic alignment:
  - `docs/pilot/phase10-parity-continuity.json`
  - `docs/pilot/phase10-migration-continuity.json`
  - `docs/pilot/phase10-operational-slo-continuity.json`
  - `tests/conformance/phase10-parity-continuity.test.ts`

- Spec usability:
  - `docs/pilot/phase5-spec-usability-evidence.json`
  - `docs/pilot/phase8-ergonomics-report.json`
  - `docs/pilot/phase8-dsl-ergonomics-improvements.json`

- Migration executability and replay verification:
  - `docs/pilot/phase7-migration-protocol-check.json`
  - `docs/pilot/phase9-migration-drills.json`
  - `docs/pilot/phase9-migration-safety-report.json`
  - `docs/pilot/phase10-migration-continuity.json`

- Backend semantic equivalence (scoped):
  - `docs/pilot/phase9-edgecase-parity.json`
  - `docs/pilot/phase9-random-differential-sweeps.json`
  - `docs/pilot/phase10-postgres-having-harness.json`
  - `docs/pilot/phase10-continuity-report.json`

---

## 5. Governance and Phase Gates

- Phase 10 exit checklist:
  - `docs/pilot/phase10-exit-checklist.json`
- Phase 10 docs consistency gate:
  - `scripts/check_phase10_docs_consistency.sh`
  - `docs/pilot/phase10-doc-consistency.json`
- Phase 11 block gate:
  - `scripts/check_phase11_block.sh`
  - `docs/pilot/phase11-gate.json`
- Phase 10 closure report:
  - `docs/pilot/phase10-closure-report.json`

Rule:
- phase transition is valid only when checklist artifacts are `pass`.

---

## 6. Active Next Vector (Post-Phase 10)

Canonical next sequence:
1. Freeze Phase 11 scope and objective checklist.
2. Expand objective scorecard from pilot envelope to broader deployment evidence.
3. Close remaining deferred SQL/parity items or formally re-gate them.
4. Preserve one-checkbox/one-commit governance discipline.

Source of truth:
- `PHASE10.md`
- `ROADMAP.md` section `AA`
- `docs/pilot/objective-scorecard-phase10.md`

Execution policy:
- one checkbox = one commit,
- include code + tests + docs + artifact evidence in the same checkbox commit.

---

## 7. Canonical References

- Mission and working rules: `AGENTS.md`
- Global execution plan: `ROADMAP.md`
- Current phase closure: `PHASE10.md`
- Lean kernel milestones: `LEAN_KERNEL_V4.md`
- Objective scorecard: `docs/pilot/objective-scorecard-phase10.md`
