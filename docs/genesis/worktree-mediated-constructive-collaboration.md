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

> **Implementation Note (2026-02-15):** The WMCC protocol was simplified from a 
> complex message-passing system (59 scripts, 6 models, 24,000 lines) to direct 
> state management (6 scripts, 2 files, ~300 lines). The conceptual framework 
> below remains valid, but specific mechanisms (message_events, evidence bindings,
> auto-dispatch loops) have been replaced with simpler equivalents.
> See `AGENTS.md` for current operational guidance.

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

**Guarantee 4 — Governed Dispatch Authority**  
Dispatch authority is constrained by worktree governance:
- one owner per worktree,
- assignment-dispatch messages must be emitted by the owner of the source
  worktree,
- worktree creation authority is explicitly declared.

**Guarantee 5 — Synchronization as Proof Obligation**  
Synchronization is not operational courtesy; it is a validity condition for
collaboration transitions.

For any worker-side mutation `μ` (claim/fulfill/revert), admissibility requires:
- binding to `base_main_commit`,
- binding to `message_ref`,
- binding to `expected_from_status`.

A transition is accepted iff all three bindings match canonical state at
write-time. Preflight success alone is insufficient.

Consequences:
- fetch/rebase freshness checks are mandatory before action,
- transition writes must re-check lifecycle preconditions atomically,
- stale writes fail closed and are retried only after re-sync and re-read.

This closes the semantic cavity where a worker acts on stale projections while
still producing structurally valid events.

## 5. Role Authority Model

WMCC defines two collaboration roles with asymmetric authority:

**Main (AGENT_MAIN)**
- Holds **dispatch authority**: decides what work is assigned and to whom
- Holds **completion authority**: decides when fulfilled work is accepted (ingest/close)
- Holds **governance authority**: promotes workflow phases, triages friction requests
- Holds **delegation authority**: assigns worktree ownership
- **Proactive**: drives workflow state, orchestrates execution

**Worker (AGENT_*)**
- Holds **execution authority**: implements assigned scope on bound branch
- **Reactive**: claims dispatched work, fulfills with evidence, reports friction
- Cannot self-assign, self-validate completion, or promote workflow phases

**Separation of Concerns**

| Decision | Authority | Rationale |
|----------|-----------|-----------|
| What gets worked on | Main | Maintains coherent workflow priority |
| Who does the work | Main | Balances load, matches capabilities |
| When work is accepted | Main | Ensures gate compliance before convergence |
| Phase promotion | Main | Controls milestone workflow transitions |
| Friction disposition | Main | Resolves blockers, accepts/rejects requests |
| How work is implemented | Worker | Autonomous execution within scoped bounds |
| Evidence quality | Worker | Responsible for proof of completion |

This asymmetry ensures constructive evolution: Main maintains coherent
workflow state; Workers maintain coherent implementation state. Neither can
unilaterally claim completion or bypass validation.

### 5.1 Architectural Limitations and Tradeoffs

WMCC makes explicit tradeoffs that create boundaries on full automation:

**Git/YAML as Event Store (Transparency over Transactions)**
- We chose human-readable YAML files in Git over a database with ACID transactions
- This provides auditability and accessibility but means we cannot implement true atomicity
- A failed claim+fulfill sequence cannot be rolled back atomically; we can only append compensating events
- Consequence: Some edge cases (race conditions, orphaned events) require manual intervention

**Consistency over Availability (Correctness over Automation)**
- The system validates preconditions before mutation and fails closed on conflict
- We do not auto-retry indefinitely because retries without understanding the failure mode can amplify errors
- Consequence: Circuit breakers trip; human judgment is required for recovery

**Human Judgment for Ambiguous Cases**
- Friction triage, phase promotion, and evidence quality assessment require semantic understanding
- Automating these would require either: (a) perfect error classification (unsolved), or (b) accepting wrong decisions (unacceptable)
- Consequence: 5% of operations require human decision; the system detects and escalates these cases

**Distributed by Design**
- Multiple agents (Main, Workers) mutate shared state
- Without distributed transactions (2PC, Paxos), race conditions are possible
- The protocol detects races (via at_seq ordering and lifecycle validation) but cannot prevent all of them
- Consequence: Orphaned events can occur; automated repair handles common patterns but not all

**Implication for Agent Operators**
The system is designed to be *resilient* (detects failures, provides recovery paths) not *autonomous* (handles all cases without intervention). This is a deliberate choice: we prefer explicit failure modes over silent automation errors.

## 6. First-principles grounding

- **State machine discipline**: collaboration is modeled as valid/invalid
  transitions over worktree states.
- **Control by admissibility**: only gate-satisfying transitions are admitted.
- **Information locality**: obligation/evidence packets reduce ambiguity at
  handoff boundaries.
- **Compositionality**: local validated transitions compose into global progress.

## 7. Role of branches

Branches are intentionally not semantic authorities.
They serve as:

- isolation lanes for bounded change units,
- typed message envelopes (naming conventions),
- replayable evidence containers before ingestion.

After successful ingestion, branch retention has no semantic value and should
default to deletion.

## 8. Implementation projection in this repository

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
- owner-dispatch authority for assignment dispatch kinds,
- branch naming constraints,
- payload/evidence path existence (where path-like).

Operationally, collaboration flow is projected as generated inbox/outbox views
per worktree in `worktree-mailboxes.generated.json`.

Normative operator loop:
- each worktree starts from mailbox projection, not ad hoc local task notes,
- messages are consumed from inbox while actionable states exist,
- lifecycle progress is represented only via append-only `message_events`.
- `WORKTREE_ASSIGNMENT.md` is outside WMCC protocol and must not be used as
  task authority.

Message lifecycle states currently supported:

- `queued`, `sent`, `acknowledged`, `fulfilled`,
- `rejected`, `rescinded`, `ingested`, `closed`.

Assignment closure semantics include explicit outcomes:
- `pending`
- `fulfilled_by_assignee`
- `fulfilled_by_main`
- `blocked`

`fulfilled` is not only a lifecycle marker. It is discharge-bearing:
- fulfilled events must carry typed evidence bindings (`evidence_kind_ref`),
- assignment claim kind determines required obligation profile(s),
- obligation evidence minima are checked during cross-model validation.

## 9. Failure modes

- agent-centric coordination with no worktree-bound obligations
- branch completion claims without canonical gate evidence
- handoff claims not mapped to typed obligation profiles
- stale helper branches treated as progress truth

Each failure mode weakens constructive collaboration guarantees.

## 10. Scope and limits

- WMCC governs collaboration semantics inside the declared repository process.
- It does not replace CICSC semantic proofs.
- It does not guarantee correctness of obligations that are underspecified.
- Current protocol checks type/structure and obligation evidence minima;
  it does not yet cryptographically verify artifact digests against bytes.

## 11. Summary

WMCC is the collaboration semantics for constructive evolution workflows.
If CICSC defines what is right and CIECP defines how rightness survives change,
WMCC defines how multiple executors coordinate that change without losing
semantic control.

## Appendix: Message-Passing Sequence Diagram

See:
- `docs/genesis/worktree-collab-sequence.md`
- `docs/genesis/worktree-collab-sequence.mmd` (raw source)

This Mermaid sequence diagram captures the normative mailbox-driven WMCC flow:
dispatch, acknowledge, fulfill with evidence, ingest, close, and rescind path.
