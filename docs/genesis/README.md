# Genesis Stack: CIS -> CICSC -> CIECP -> WMCC (+ CAM)

This directory captures the conceptual top of the project.

Genesis documents are intentionally prose artifacts.
They define semantic intent for humans (and model-ingesting agents), then that
intent is projected into machine-checkable control-plane models.

In this repository, these four documents/functions are treated as a strict stack,
plus one progression method:

1. `docs/genesis/on-constructively-invariant-systems.md`
2. `docs/genesis/constructively-invariant-control-system-compiler.md`
3. `docs/genesis/constructive-invariance-evolution-control-plane.md` + `control-plane/*` runtime/gate models
4. `docs/genesis/worktree-mediated-constructive-collaboration.md` + active control-plane runtime surfaces
5. `docs/genesis/boundary-contraction.md`
6. `docs/genesis/constructive-accretion-method.md`
7. `docs/genesis/on-agent-ergonomics.md`

Where:
- `CIS` = Constructively Invariant Systems
- `CICSC` = Constructively Invariant Control System Compiler
- `CIECP` = Constructive-Invariance Evolution Control Plane
- `WMCC` = Worktree-Mediated Constructive Collaboration
- `CAM` = Constructive Accretion Method
- `AE` = Agent Ergonomics

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

### 3) CIECP: Constructive-Invariance Evolution Control Plane (`control-plane/*`)
Role: **execution-governance layer**.

Implements executable governance over CICSC evolution:
- objective model,
- capability model,
- canonical execution ledger,
- gate model and machine checks.

In project terms: CIECP is "how change is allowed while preserving what is right."

### 4) WMCC: Worktree-Mediated Constructive Collaboration (`worktree-mediated-constructive-collaboration.md` + control-plane runtime)
Role: **collaboration protocol layer**.

Defines typed collaboration contracts for multi-worktree execution:
- worktree-bound handoff semantics,
- obligation/evidence typing,
- branch-as-transport and canonical-ingestion discipline.
- protocol event transport over canonical runtime state (`state/ledger.db`)
  via `agentd`, `autoassign`, `worker-run-assignment`, `integrate`, and `status`.

In project terms: WMCC is "how multiple executors coordinate admissible change."

### 5) Boundary Contraction (`boundary-contraction.md`)
Role: **categorical discipline layer**.

The categorical discipline that makes WMCC constructive:
- Constrains integration to FF-morphisms only
- Invalid structural states become unreachable by construction
- See `lean/Cicsc/Evolution/FFIntegration.lean` for formal proofs
- See `control-plane/integrate.sh` for executable implementation

## Relationship Contract

Composition is one-way and vertical:

- `CIS -> CICSC -> CIECP -> WMCC`

Meaning:
- CIS constrains the semantics CICSC must realize.
- CICSC constrains the invariants CIECP must protect during change.
- CIECP must never redefine CIS/CICSC semantics; it only operationalizes and enforces them.
- WMCC must never redefine CIECP policy semantics; it only constrains collaboration execution paths.
- CAM is orthogonal to the stack: it constrains the sequencing discipline used to grow all layers.
- AE is orthogonal to the stack: it constrains how executable collaboration is made low-friction without changing semantics.

## Repo-Level Practical Rule

When there is tension:

1. Preserve CIS/CICSC semantic invariants first.
2. Adjust CIECP process artifacts (ledger/gates/views) second.
3. Never accept process convenience that weakens semantic correctness.
