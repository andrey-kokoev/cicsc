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

This document captures what was learned while operationalizing work assignment.

- CIS defines invariance as principle.
- CICSC defines semantic truth.
- CIECP defines admissible evolution under evidence.
- Agent ergonomics defines how likely executors are to follow the protocol correctly on first try.

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
For the current system this is `control-plane/assignments.yaml`.

### B. Complexity must match the problem

**First attempt (v1):** Built a distributed consensus protocol with:
- Message passing (sent → acknowledged → fulfilled → ingested → closed)
- Cryptographic evidence bindings
- Role authority models
- Auto-dispatch loops with circuit breakers
- 24,000 lines of code

**Problem:** We had 2-3 agents on the same machine editing files in a shared git repo.
The complexity exceeded requirements and caused data integrity issues.

**Second attempt (v2):** Direct state management with:
- Two YAML files (execution-ledger.yaml, assignments.yaml)
- Six shell scripts
- Git history as audit trail
- ~300 lines of code

**Lesson:** Match the solution to the actual constraints, not theoretical ones.

### C. Git is already a database

We tried to build:
- Immutable event sourcing (git already has this)
- Content-addressed evidence (git objects are this)
- Concurrent access control (git merge/rebase handles this)

**Lesson:** Use existing tools rather than reimplementing their features.

### D. Validation is more valuable than enforcement

Complex protocols try to prevent errors through structure.
Simpler systems:
- Allow direct edits
- Validate before commit
- Fail fast with clear errors

**Lesson:** `./control-plane/validate.sh` is more maintainable than 42 scripts enforcing rules.

## 4. Current simplification

The collaboration system was reduced to:

1. **execution-ledger.yaml** - Roadmap (phases, milestones, checkboxes)
2. **assignments.yaml** - Work queue (checkbox, agent, status)
3. **Six commands** - dispatch, claim, complete, inbox, check_gates, validate

This removes:
- Message events
- Evidence bindings  
- Role authority
- Worktree delegation
- Friction requests
- Auto-dispatch loops
- Circuit breakers

While preserving:
- Checkbox tracking
- Assignment to agents
- Gate validation
- Git-based audit trail

## 5. Protocol stability

Simpler protocols are more stable because:
- Fewer moving parts
- Direct mapping to git operations
- Clear error messages
- Human-readable state

The current system can be understood by reading two YAML files.
The previous system required understanding 6 interlocking models.
