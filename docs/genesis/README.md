# Genesis Stack: CIS -> CICSC -> EGoCI

This directory captures the conceptual top of the project.

In this repository, these three documents/functions are treated as a strict stack:

1. `docs/genesis/on-constructively-invariant-systems.md`
2. `docs/genesis/constructively-invariant-control-system-compiler.md`
3. `control-plane/README.md` (with `control-plane/*` models)

## What They Really Are

### 1) CIS (`on-constructively-invariant-systems.md`)
Role: **theory layer**.

Defines the abstract idea of constructively invariant systems:
- what must be preserved under transformation,
- why transformations must be constructive (not best-effort),
- and the formal posture for invariance-preserving evolution.

In project terms: CIS is the normative semantic horizon.

### 2) CICSC (`constructively-invariant-control-system-compiler.md`)
Role: **semantic system design layer**.

Defines CICSC as a concrete instantiation of CIS:
- Spec/IR/history/reducers/constraints/migrations calculus,
- compatibility and semantic closure requirements,
- invariance expectations for compile + migrate + cutover.

In project terms: CICSC is "what is right" semantically for this system.

### 3) EGoCI (`control-plane/README.md` + `control-plane/*`)
Role: **execution-governance layer**.

Implements executable governance over CICSC evolution:
- objective model,
- capability model,
- canonical execution ledger,
- gate model and machine checks.

In project terms: EGoCI is "how change is allowed while preserving what is right."

## Relationship Contract

Composition is one-way and vertical:

- `CIS -> CICSC -> EGoCI`

Meaning:
- CIS constrains the semantics CICSC must realize.
- CICSC constrains the invariants EGoCI must protect during change.
- EGoCI must never redefine CIS/CICSC semantics; it only operationalizes and enforces them.

## Repo-Level Practical Rule

When there is tension:

1. Preserve CIS/CICSC semantic invariants first.
2. Adjust EGoCI process artifacts (ledger/gates/views) second.
3. Never accept process convenience that weakens semantic correctness.
