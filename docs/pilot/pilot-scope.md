# Pilot Scope Contract

## Pilot Vertical

Ticketing workflow (single-tenant first, multi-tenant exercised in staging).

## Objective

Validate CICSC invariants under real operator usage before opening new research axes.

## In Scope

- Ticket lifecycle commands: create, triage, close.
- Snapshot + bool_query constraints already in supported subset.
- View execution for operational board/reporting queries.
- Replay verification loop per deploy and per migration rehearsal.

## Out of Scope

- New query operators beyond current supported subset.
- Custom bundle-specific runtime branches.
- Multi-region semantics.
- Postgres production rollout in this pilot.

## Success Criteria

- No invariant-violating writes accepted in pilot window.
- Replay verification remains stable and deterministic.
- All observed gaps are captured as execution-ledger checkboxes, not hotfix drift.
- Zero bundle-specific hacks introduced.

## Exit Criteria for Pilot Scope

- At least one full workflow cycle completed by real operators.
- Drift/performance/missing-primitive findings published in pilot findings report.
