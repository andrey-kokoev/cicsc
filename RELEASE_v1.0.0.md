# CICSC v1.0.0 Release

This release marks completion of the roadmap through validation, formalization, kernel extraction, and governance artifacts.

## Included

- Invariant-preserving runtime and compiler workflow
- Spec DSL + Core IR + adapter conformance layers
- Migration transform + replay verification + cutover protocol
- Canonical verticals (Kanban, Ticketing, CRM) and demo datasets
- Formal semantics and normative specification references
- Extracted kernel surface and memory backend

## Tag

`v1.0.0`

## v1.5 Coherency Closure Addendum

Post-v1.0.0 Lean kernel coherency closure completed:
- Canonical constraint evaluator surface unified on `holdsConstraint`
- Executable checker soundness bridged (`checkTypeSpec -> WFTypeSpec`, `checkIR -> WFIR`)
- Replay WF preservation theorems shifted to `WFTypeSpec` assumptions
- Declarative `HasType` restored with algorithmic soundness bridge
- Versioning and naming clarified (Lean-kernel milestone vs IR schema version)

## Lean v4 + Phase 6 Status Addendum

Current repository status after v1.0.0:
- Lean kernel milestones through `LEAN_KERNEL_V4.md` are completed (scoped where documented).
- Phase 6 governance closure is complete (`PHASE6.md` all checked, `ROADMAP.md` W-series all checked).
- Phase transition gating is artifact-driven via:
  - `docs/pilot/phase6-exit-checklist.json`
  - `docs/pilot/phase7-gate.json`
  - `scripts/check_phase7_block.sh`
