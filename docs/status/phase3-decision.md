# Phase 3 Decision Record

Date: 2026-02-12

## Decision

- Do **not** freeze core as bugfix-only v1.x yet.
- Open exactly one next research axis: **Incremental verification at scale**.

## Rationale

- Exit checklist is currently failing due unresolved semantic and tooling blockers.
- Freezing now would lock unresolved correctness debt.
- Incremental verification is the least disruptive next axis and directly supports pilot operational reliability.

## Preconditions Before Axis Work Starts

- Close ROADMAP section `T` item 1 (oracle replay + constraints regression).
- Close ROADMAP section `T` item 2 (dependency/bootstrap policy).

## Enforcement

- No multi-axis research branching until this single axis has a scoped execution plan.
