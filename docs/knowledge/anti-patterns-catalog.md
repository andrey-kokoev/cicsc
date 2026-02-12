# Anti-Patterns and Failure Modes Catalog

## Anti-Pattern 1: Bundle-specific runtime logic

Failure mode: semantic leakage and non-portable behavior.

## Anti-Pattern 2: Runtime-only validation

Failure mode: late failures and silent invariant drift.

## Anti-Pattern 3: Partial migrations

Failure mode: unreplayable history and cutover inconsistency.

## Anti-Pattern 4: Non-deterministic reducers

Failure mode: replay divergence across runs/adapters.

## Anti-Pattern 5: SQL-only semantics in Spec/IR

Failure mode: oracle/backends mismatch and non-conformance.
