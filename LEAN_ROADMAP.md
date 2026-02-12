# CICSC Lean Kernel Roadmap (Derived from LEAD_KERNEL_V0.md)

## A. Lean Scaffold
- [x] Create `lean/` workspace scaffold and module layout
- [x] Add Lean project configuration (`lakefile.lean`, root module)

## B. Core Syntax and Types
- [x] Define kernel syntax in `Cicsc/Core/Syntax.lean` (Expr, Query, ReducerOp, IR)
- [x] Define value/type domains in `Cicsc/Core/Types.lean` (Val, Ty, Env, State)
- [x] Define events/history/state primitives in syntax/types with typed records

## C. Semantics
- [x] Implement expression evaluator in `Semantics/ExprEval.lean`
- [x] Implement replay fold semantics in `Semantics/Replay.lean`
- [x] Implement constraint semantics in `Semantics/Constraints.lean`
- [x] Implement abstract command semantics in `Semantics/Commands.lean`

## D. Meta and Typechecking
- [x] Add decidable typechecker skeleton in `Meta/Typecheck.lean`
- [x] Add typing judgments for Expr subset and well-typed env relation

## E. Proof Milestone v0
- [x] Prove expression evaluation determinism theorem
- [x] Prove replay totality theorem
- [x] Prove reducer well-formedness preservation theorem

## F. Migration Formalization
- [x] Define migration primitives in `Evolution/Migration.lean`
- [x] Prove naturality/commuting-diagram theorem in `Evolution/Naturality.lean`

## G. Examples and Closure
- [x] Add Ticketing example in `Examples/Ticketing.lean`
- [x] Add Kanban example in `Examples/Kanban.lean`
- [x] Add Lean kernel acceptance checklist document (maps to v0 acceptance criteria)

## H. Evolution Milestone
- [x] Make migration event handling total (unknown transform falls back to identity; `none` means explicit drop only)
- [x] Add `WFMigration` predicate with coverage/target/state validity checks
- [x] Replace naturality tautology with real theorem statement (`replay_commutes`)
- [x] Prove `replay_commutes` by induction on `History`
- [ ] Add non-identity Ticketing v0→v1 migration example proof (event + state rename)
