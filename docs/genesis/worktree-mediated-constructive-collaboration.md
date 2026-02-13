---
title: "Worktree-Mediated Constructive Collaboration"
description: "A typed collaboration protocol where Git worktrees are execution boundaries and branch handoffs are evidence-bearing morphisms."
date: "2026-02-13"
tags:
  - concepts
  - systems
  - collaboration
  - governance
  - control-theory
draft: false
---

# Worktree-Mediated Constructive Collaboration (WMCC)

A constructive collaboration model in which Git worktrees, not chat sessions,
are the primary execution boundaries for change.

## 1. Positioning

This document defines WMCC as a collaboration protocol within CIECP.

- CIS defines invariance as principle.
- CICSC defines semantic truth of the system.
- CIECP defines admissible evolution under evidence.
- WMCC defines how multiple executors coordinate changes without violating that evolution contract.

Operationally, a collaboration handoff `H` is valid only when:

accept(H) iff typed_obligations(H) are satisfied  
and required evidence is attached to the handoff branch/commit path.

## 2. Why worktree centrality

Agent identity is necessary but insufficient for semantic control.
The enforceable boundary is the mutable state container where code evolves.
In this repository, that boundary is a Git worktree.

Therefore:

- `Agent` is accountability metadata.
- `GitWorktree` is operational state boundary.
- `Branch` is transport lane for bounded deltas.
- `Main` is canonical convergence state.

## 3. Collaboration calculus

Minimal collaboration algebra:

- node: worktree state
- message: typed obligation/evidence packet
- channel: branch and commit path
- validator: gates and model checks
- merge operator: canonical ingestion to `main`
- feedback: rejection reasons mapped to next obligations

A collaboration transition is admissible only if validation is constructive and
replayable from repository state.

## 4. Core operational guarantees

**Guarantee 1 — Typed Handoff**  
Every cross-worktree change must map to explicit claim kinds, obligation
profiles, and evidence classes.

**Guarantee 2 — Evidence-Bound Transport**  
A branch is not truth; it is a carrier. Truth is established only by successful
canonical gate execution on ingestion.

**Guarantee 3 — Ephemeral Lanes, Stable Convergence**  
Work branches are disposable after ingestion. Semantic continuity is retained
in the canonical convergence branch and execution ledger.

## 5. First-principles grounding

- **State machine discipline**: collaboration is modeled as valid/invalid
  transitions over worktree states.
- **Control by admissibility**: only gate-satisfying transitions are admitted.
- **Information locality**: obligation/evidence packets reduce ambiguity at
  handoff boundaries.
- **Compositionality**: local validated transitions compose into global progress.

## 6. Role of branches

Branches are intentionally not semantic authorities.
They serve as:

- isolation lanes for bounded change units,
- typed message envelopes (naming conventions),
- replayable evidence containers before ingestion.

After successful ingestion, branch retention has no semantic value and should
default to deletion.

## 7. Implementation projection in this repository

WMCC is operationalized through control-plane collaboration artifacts:

- `control-plane/collaboration/collab-model.yaml`
- `control-plane/collaboration/collab-model.schema.json`
- `control-plane/scripts/validate_collab_model.sh`
- `scripts/check_collaboration_model.sh`
- `control-plane/views/worktree-mailboxes.generated.json`

Cross-model checks bind collaboration contracts to objectives, capabilities, and
execution-ledger checkbox scope.

### Typed message transport and mailbox projection

Current WMCC implementation includes explicit typed message transport:

- `message_kinds`: protocol-level message categories.
- `messages`: concrete routed packets bound to assignments.

Messages are validated against:
- assignment references,
- agent/worktree ownership consistency,
- branch naming constraints,
- payload/evidence path existence (where path-like).

Operationally, collaboration flow is projected as generated inbox/outbox views
per worktree in `worktree-mailboxes.generated.json`.

Normative operator loop:
- each worktree starts from mailbox projection, not ad hoc local task notes,
- messages are consumed from inbox while actionable states exist,
- lifecycle progress is represented only via append-only `message_events`.

`WORKTREE_ASSIGNMENT.md` can exist as a local convenience memo but is not part
of WMCC protocol truth.

Message lifecycle states currently supported:

- `queued`, `sent`, `acknowledged`, `fulfilled`,
- `rejected`, `ingested`, `closed`.

## 8. Failure modes

- agent-centric coordination with no worktree-bound obligations
- branch completion claims without canonical gate evidence
- handoff claims not mapped to typed obligation profiles
- stale helper branches treated as progress truth

Each failure mode weakens constructive collaboration guarantees.

## 9. Scope and limits

- WMCC governs collaboration semantics inside the declared repository process.
- It does not replace CICSC semantic proofs.
- It does not guarantee correctness of obligations that are underspecified.

## 10. Summary

WMCC is the collaboration semantics for constructive evolution workflows.
If CICSC defines what is right and CIECP defines how rightness survives change,
WMCC defines how multiple executors coordinate that change without losing
semantic control.
