# Lean Kernel v0 Acceptance Checklist

Derived from `LEAD_KERNEL_V0.md` acceptance criteria.

- [x] `replay` is definitional and total for known type streams (`Replay.lean`)
- [x] Expr determinism theorem exists (`ExprEval.lean`)
- [x] Reducer well-formedness preservation theorem scaffold exists (`Replay.lean`)
- [x] Migration primitives are defined (`Evolution/Migration.lean`)
- [x] Naturality/commutation theorem scaffold exists (`Evolution/Naturality.lean`)
- [x] Ticketing example module exists (`Examples/Ticketing.lean`)
- [x] Kanban example module exists (`Examples/Kanban.lean`)
- [ ] `lake build` proof check executed in environment with Lean toolchain

## Notes

- Repository now contains a complete Lean kernel structure and proof scaffolding.
- Final theorem strengthening and full build verification can be iterated incrementally.
