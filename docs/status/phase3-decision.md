# Phase 3 Decision Record

Date: 2026-02-12

## Decision

- Do **not** freeze core as bugfix-only v1.x yet.
- Open exactly one next research axis: **Incremental verification at scale**.

## Rationale

- Stabilization gates now pass (baseline + CI target + deterministic bootstrap).
- Full sqlite execution parity matrix is still incomplete; freezing now would lock unresolved backend-conformance debt.
- Incremental verification is the least disruptive next axis and directly supports pilot operational reliability.

## Preconditions Before Axis Work Starts

- Keep SQL execution-vs-oracle smoke differential as required gate.
- Reduce failures in `tests/conformance/sqlite-exec-vs-oracle.test.ts` to full pass before declaring backend-conformance closure.

## Enforcement

- No multi-axis research branching until this single axis has a scoped execution plan.
