# Backend NULL/Ordering/Collation Policy (v1)

This document declares backend semantic deltas that must be handled explicitly in
cross-backend conformance checks.

Source of truth:
- `tests/conformance/backend-semantics-policy.json`

## Scope

- SQLite vs Postgres default NULL ordering differences.
- SQLite binary collation vs Postgres locale-dependent collation.
- Oracle interpreter normalization expectations used by differential tests.

## Rules

- Deterministic query assertions must include explicit `order_by`.
- Differential tests may canonicalize row order only when ordering is out of scope.
- String ordering should be treated as backend-specific unless explicitly modeled.
- Known deltas must be listed and reviewed before tightening parity gates.
