# PHASE_LEVEL_ROADMAP.md

This document is a phase-level planning map.
It is intentionally non-executable and non-status-bearing.

Canonical status truth remains `ROADMAP.md` only.

## Data Ownership Model

- `ROADMAP.md`: canonical execution ledger (checkbox status truth)
- `PHASE*.md`: derived status views that must mirror `ROADMAP.md`
- `PHASE_LEVEL_ROADMAP.md`: trajectory planning only (no status checkboxes)
- `JOURNEY_VECTOR.md`: objective-to-evidence navigation only (no status checkboxes)

## Completed Journey (Historical)

Completed canonical phases in `ROADMAP.md`:
- `T` (Phase 3)
- `U` (Phase 5)
- `W` (Phase 6)
- `X` (Phase 7)
- `Y` (Phase 8)
- `Z` (Phase 9)
- `AA` through `AT` (Phases 10 through 29)

Current gate state:
- Phase 30 gate is open (`docs/pilot/phase30-gate.json`)

## Forward Sequence to Completion

Planned phase sequence from current position:
- `AU` Phase 30: Spec DSL completion and authoring safety
- `AV` Phase 31: Migration guarantees and cutover protocol hardening
- `AW` Phase 32: Backend equivalence completion (SQLite/D1 + Postgres)
- `AX` Phase 33: Lean/runtime semantic lockstep and evidence extraction
- `AY` Phase 34: Meta-compiler interface and bundle registry productization
- `AZ` Phase 35: Field completion and objective scorecard closure
- `BA` Phase 36: Project completion and steady-state handoff

## Milestone Skeleton (Planning Only)

Each forward phase follows the same milestone pattern:
- `<PhaseCode>1` Scope freeze and baseline continuity
- `<PhaseCode>2` Primary validation closure for that phase theme
- `<PhaseCode>3` Hardening/operationalization for that phase theme
- `<PhaseCode>4` Governance closure and next-phase gate

Execution status for these milestones must be created and tracked in `ROADMAP.md`
before implementation starts.

## Operational Rule

To avoid workflow-data duplication:
- never place execution checkboxes in this file,
- never mark status here,
- use this file only for sequence design and dependency reasoning.
