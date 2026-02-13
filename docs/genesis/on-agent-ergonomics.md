---
title: "On Agent Ergonomics"
description: "What we learned about making constructive collaboration executable and low-friction for agents."
date: "2026-02-13"
tags:
  - concepts
  - systems
  - collaboration
  - ergonomics
  - governance
draft: false
---

# On Agent Ergonomics

Agent ergonomics is not UI polish.
It is the degree to which a correct action is the easiest action.

In this project, ergonomics matters because collaboration mistakes are semantic
mistakes: they can break authority, evidence, or progress coherence.

## 1. Positioning

This document captures what was learned while operationalizing WMCC.

- CIS defines invariance as principle.
- CICSC defines semantic truth.
- CIECP defines admissible evolution under evidence.
- WMCC defines typed collaboration.
- Agent ergonomics defines how likely executors are to follow WMCC correctly on first try.

Ergonomics quality is therefore part of semantic reliability, not a secondary concern.

## 2. Core thesis

For constructive collaboration, the protocol must be:

- explicit enough to be checkable,
- minimal enough to be routinely followed,
- discoverable enough to be usable without oral tradition.

When any of these is missing, semantic air pockets appear: behavior exists in
practice but not in the formal protocol.

## 3. What we learned

### A. Single canonical entry point is non-negotiable

Agents need one place to start execution.
For WMCC this is the generated mailbox projection:

- `control-plane/views/worktree-mailboxes.generated.json`

Without a single entry point, local notes become shadow authority.

### B. Messages must be immutable

State updates are represented as append-only lifecycle events.
This preserves replayability and auditability and avoids hidden in-place edits.

### C. Wrapper commands are semantic infrastructure

Typed scripts are not convenience glue; they are safety rails:

- `collab_dispatch.sh`
- `collab_claim_next.sh`
- `collab_fulfill.sh`
- `collab_close_ingested.sh`
- `collab_delegate_worktree.sh`
- `collab_run_once.sh`
- `collab_help.sh`

They reduce discretionary interpretation by constraining action shape.

### D. Authority must be explicit and delegable

Single-owner worktree governance with typed delegation/revocation closes an
important ambiguity: who can dispatch from a worktree right now.

### E. Discoverability is part of correctness

If an agent cannot quickly discover the right procedure, it will improvise.
Improvisation is an error source in constructive protocols.

Therefore:
- `AGENTS.md` must contain bootstrap + command surface + happy path.
- `control-plane/README.md` must mirror operational entry points.

## 4. Practical ergonomic contract

A worker agent should be able to run exactly this loop:

1. refresh views,
2. read actionable inbox,
3. claim one message,
4. fulfill with typed evidence,
5. stop when no actionable messages remain.

If this cannot be done in a few commands without guessing, ergonomics is not complete.

## 5. First-principles grounding

- **Control theory**: reduce control variance by reducing operator choice where
  choice is not semantically meaningful.
- **Information theory**: minimize ambiguity at handoff boundaries by structured
  message/evidence typing.
- **State-machine discipline**: represent collaboration state by explicit
  transitions, not mutable snapshots.

## 6. Failure modes to avoid

- protocol truth split across mailbox and ad hoc files
- in-place mutation of message envelopes
- undocumented authority transfer
- “expert-only” execution flow requiring tribal knowledge

Each of these increases semantic leakage between intended and actual process.

## 7. Scope and limits

- Ergonomic quality improves protocol adherence probability; it does not replace
  semantic proofs or gate checks.
- Current ergonomics is optimized for repository-local agent execution.
- Human-friendly UX layers can be added later, but must compile down to the
  same typed WMCC primitives.

## 8. Summary

Agent ergonomics in constructive collaboration is the engineering of
low-friction correctness.
The target is simple: doing the right thing must be easier than doing anything else.
