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
