# ADR-001: Lean Kernel Conformance

## Status
Accepted

## Context
CICSC is a critical system handling socio-technical invariants. We need a way to ensure that the core runtime execution (commands, reducers, constraints) is semantically correct and remains so as we optimize backend implementations (SQLite, Postgres).

## Decision
We use a Lean 4 formal model as the "Gold Standard" or "Oracle". 
1. The kernel semantics (typing of Core IR, evaluator for expressions, and reducer transitions) are defined in Lean.
2. We derive a reference interpreter in TypeScript from this model.
3. Every backend implementation must pass differential conformance tests against this reference interpreter.

## Consequences
- **Pros**: Provable correctness of core logic; prevents regression in backend lowerings.
- **Cons**: High barrier to entry for changing core semantics (requires Lean updates); performance overhead of differential testing in CI.
