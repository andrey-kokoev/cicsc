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
- Phase status: Phase 6 complete (`PHASE6.md` all checked).
- Roadmap status: `W` section complete; Phase 7 `X` section opened (`ROADMAP.md`).
- Governance status: Phase 7 gate is artifact-driven (`docs/pilot/phase7-gate.json`).

---

## 3. Journey Timeline

1. Foundation and runtime hardening: complete.
2. Lean coherency closure and scoped formal expansion: complete through v4.
3. Field hardening and pilot evidence loops: complete through Phase 6.
4. Semantic equivalence hardening: planned in Phase 7 (next active vector).

---

## 4. Objective-to-Evidence Map

- Invariants under concurrency:
  - `docs/spec/isolation-guarantees.md`
  - `docs/pilot/phase6-concurrency-conformance.json`
  - `tests/concurrency/transaction-model.test.ts`
  - `tests/concurrency/causality-replay.test.ts`

- IR/runtime semantic alignment:
  - `docs/spec/truth-audit-v1.md`
  - `docs/spec/formal-backend-conformance.md`
  - `tests/conformance/sqlite-exec-vs-oracle.test.ts`
  - `tests/conformance/postgres-exec-vs-oracle.test.ts`

- Spec usability:
  - `docs/pilot/phase5-spec-usability-evidence.json`
  - `tests/spec/reference-vertical-usability.test.ts`
  - `tests/spec/reference-vertical-crm-usability.test.ts`

- Migration executability and replay verification:
  - `docs/pilot/phase5-migration-drill-evidence.json`
  - `docs/pilot/phase6-migration-concurrency-drill.json`
  - `tests/oracle/migration-preflight.test.ts`
  - `tests/oracle/migration-dry-run.test.ts`
  - `tests/oracle/cutover-protocol.test.ts`
  - `tests/oracle/rollback-workflow.test.ts`

- Backend semantic equivalence (scoped):
  - `docs/pilot/phase6-required-gates.json`
  - `docs/pilot/compatibility-matrix.md`
  - `tests/conformance/cross-backend-differential.test.ts`

---

## 5. Governance and Phase Gates

- Phase 6 exit checklist:
  - `docs/pilot/phase6-exit-checklist.json`
- Phase 7 block gate:
  - `scripts/check_phase7_block.sh`
  - `docs/pilot/phase7-gate.json`
- Artifact consistency gate:
  - `scripts/check_phase6_artifact_gates.sh`

Rule:
- phase transition is valid only when checklist artifacts are `pass`.

---

## 6. Active Next Vector (Phase 7)

Canonical next sequence:
1. `X1` Cross-backend semantic parity hardening.
2. `X2` Concurrency/isolation strengthening.
3. `X3` Migration/operational contract hardening.
4. `X4` Governance gate for Phase 8.

Source of truth:
- `PHASE7.md`
- `ROADMAP.md` section `X`

Execution policy:
- one checkbox = one commit,
- include code + tests + docs + artifact evidence in the same checkbox commit.

---

## 7. Canonical References

- Mission and working rules: `AGENTS.md`
- Global execution plan: `ROADMAP.md`
- Current and next phase plans: `PHASE6.md`, `PHASE7.md`
- Lean kernel milestones: `LEAN_KERNEL_V4.md`
- Evidence-backed semantic status: `docs/spec/truth-audit-v1.md`
