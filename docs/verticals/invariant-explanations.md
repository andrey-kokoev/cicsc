# Invariant Explanations for Canonical Verticals

## Kanban

- WIP limit constraint is expressed as `bool_query` on `in_progress` lane cardinality.
- Allowed transitions are monotonic lane transitions (`backlog -> in_progress -> review -> done`).
- Replay invariant: lane occupancy is derivable solely from event history + reducer fold.

## Ticketing

- Escalation and closure transitions are guarded by state predicates.
- SLA declarations bound response and resolution windows to explicit event pairs.
- Replay invariant: escalation level and resolution state are deterministic reducer outputs.

## CRM

- Stage progression is constrained by explicit transition commands.
- Ownership and conversion signals are materialized as attrs/shadows.
- Replay invariant: conversion metrics are folds over won/lost terminal events.
