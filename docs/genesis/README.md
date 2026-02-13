# Genesis Stack: CIS -> CICSC -> CIECP -> WMCC (+ CAM)

This directory captures the conceptual top of the project.

In this repository, these four documents/functions are treated as a strict stack,
plus one progression method:

1. `docs/genesis/on-constructively-invariant-systems.md`
2. `docs/genesis/constructively-invariant-control-system-compiler.md`
3. `docs/genesis/constructive-invariance-evolution-control-plane.md` + `control-plane/README.md` (with `control-plane/*` models)
4. `docs/genesis/worktree-mediated-constructive-collaboration.md` + `control-plane/collaboration/*`
5. `docs/genesis/constructive-accretion-method.md`

Where:
- `CIS` = Constructively Invariant Systems
- `CICSC` = Constructively Invariant Control System Compiler
- `CIECP` = Constructive-Invariance Evolution Control Plane
- `WMCC` = Worktree-Mediated Constructive Collaboration
- `CAM` = Constructive Accretion Method

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

### 3) CIECP: Constructive-Invariance Evolution Control Plane (`control-plane/README.md` + `control-plane/*`)
Role: **execution-governance layer**.

Implements executable governance over CICSC evolution:
- objective model,
- capability model,
- canonical execution ledger,
- gate model and machine checks.

In project terms: CIECP is "how change is allowed while preserving what is right."

### 4) WMCC: Worktree-Mediated Constructive Collaboration (`worktree-mediated-constructive-collaboration.md` + `control-plane/collaboration/*`)
Role: **collaboration protocol layer**.

Defines typed collaboration contracts for multi-worktree execution:
- worktree-bound handoff semantics,
- obligation/evidence typing,
- branch-as-transport and canonical-ingestion discipline.
- typed message transport with generated worktree inbox/outbox projection.

In project terms: WMCC is "how multiple executors coordinate admissible change."

## Relationship Contract

Composition is one-way and vertical:

- `CIS -> CICSC -> CIECP -> WMCC`

Meaning:
- CIS constrains the semantics CICSC must realize.
- CICSC constrains the invariants CIECP must protect during change.
- CIECP must never redefine CIS/CICSC semantics; it only operationalizes and enforces them.
- WMCC must never redefine CIECP policy semantics; it only constrains collaboration execution paths.
- CAM is orthogonal to the stack: it constrains the sequencing discipline used to grow all layers.

## Repo-Level Practical Rule

When there is tension:

1. Preserve CIS/CICSC semantic invariants first.
2. Adjust CIECP process artifacts (ledger/gates/views) second.
3. Never accept process convenience that weakens semantic correctness.
