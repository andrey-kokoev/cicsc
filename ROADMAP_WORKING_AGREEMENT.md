# ROADMAP_WORKING_AGREEMENT.md

This document defines how the CICSC roadmap is to be executed.
It is process documentation for contributors and agents, not product documentation.

---

## 1. The Roadmap Is the Plan

The checklist in **`# CICSC Completion TODO (Comprehensive)`** is the canonical roadmap.

- Every checkbox corresponds to a concrete deliverable.
- No work exists outside the roadmap.
- New work enters the system only by adding new checkboxes.
- `ROADMAP.md` is the only canonical status ledger.
- `PHASE*.md` files are derived views; they may aid readability but do not own truth.

---

## 2. Atomic Work Units

Each checkbox is an atomic unit of work.

A checkbox is considered complete only when all are true:

- Code is implemented.
- Tests are added (oracle, conformance, or typechecker tests).
- Typechecker or schema generator updated if semantics changed.
- No bundle-specific logic introduced.
- Docs updated if behavior changed.

If any condition is unmet, the checkbox remains unchecked.

---

## 3. Execution Order

Work proceeds top-down by section unless explicitly blocked:

A → B → C → D → E → F → G → H → I → J → K → L → M

Within a section:
- Finish items that establish correctness and invariants before ergonomics.
- Prefer smaller correctness improvements over large feature additions.

---

## 4. Vertical Completion Over Horizontal Touching

Rules:

- Do not partially implement multiple roadmap items at once.
- Pick one checkbox and complete it end-to-end.
- Avoid touching unrelated sections in the same change.

This prevents semantic drift and half-finished invariants.

---

## 5. Invariant-First Rule

If a roadmap item introduces or modifies semantics:

- First update the IR typechecker or Spec compiler restrictions.
- Then implement runtime or lowering behavior.
- Then add conformance tests.

Never do runtime work without a static guard when one is possible.

---

## 6. Conformance Test Gate

Any change affecting:

- SQL lowering
- constraint semantics
- query semantics
- reducer semantics

must be accompanied by:

- a differential test (SQL vs oracle), or
- an oracle unit test if SQL lowering is not involved.

No exceptions.

---

## 7. No Bundle-Specific Hacks Rule

The runtime, schema generator, and lowering layers must not encode:

- Ticketing-specific logic
- CRM-specific logic
- Kanban-specific logic

If a vertical requires special behavior, that behavior belongs in:

- Spec DSL
- Core IR
- Schema generator (derived from IR)

---

## 8. Change Management

When implementation reveals missing primitives:

- Add new roadmap items.
- Add new IR primitives if needed.
- Update typechecker rules accordingly.

Do not “patch around” missing abstractions in runtime.

---

## 9. Review Checklist (Before Checking a Box)

Before marking any roadmap item complete, verify:

- [ ] Tests exist and pass
- [ ] Typechecker updated (if relevant)
- [ ] No hardcoded vertical logic introduced
- [ ] No weakening of invariants
- [ ] Docs/spec updated (if semantics changed)

---

## 10. Exit Criteria

A section of the roadmap is “complete” only when:

- All checkboxes in that section are checked
- No TODOs remain hidden in code comments
- No bundle-specific hacks remain for that layer

Only then move to the next section.

---

## 11. Non-Goals

This process explicitly rejects:

- feature-driven development without invariants
- prototype shortcuts that become permanent
- silent runtime fallbacks
- “we’ll fix it later” semantics

---

## 12. North Star

The roadmap is complete when:

> A user can describe a socio-technical system in Spec,
> compile it, deploy it, evolve it safely,
> and invariants are preserved provably over time.

All work should move the system closer to this state.

---

## 13. Commit Subject Enforcement

Commit subjects are policy-validated.

Accepted subject forms:
- `phase<phase> <milestone>[.<item>]: <summary>`
  - checkbox example: `phase12 ac3.2: add parity envelope differential harnesses`
  - phase-bootstrap example: `phase12 ac0: bootstrap phase12 plan and roadmap section`
- `<type>[/scope]: <summary>` where type is one of:
  - `docs`, `chore`, `ci`, `test`, `refactor`, `governance`, `release`

Local hook setup:
- `git config core.hooksPath .githooks`

Checks:
- local hook: `.githooks/commit-msg`
- range/CI check: `./scripts/check_commit_subjects.sh <base> <head>`
