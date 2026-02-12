# Formal Semantics: Constraint Evaluation

## Snapshot Constraints

A snapshot constraint is:

`C_s = (on_type, expr)`

Given replayed snapshot rows `Rows(on_type)`, it holds iff:

`forall r in Rows(on_type): Eval(expr, env(row=r)) == true`

## Bool Query Constraints

A bool_query constraint is:

`C_q = (on_type, args, query, assert)`

Execution:

1. Evaluate `query` over snapshot relation to produce `Q`.
2. Build assert environment with `rows_count = |Q|` and args.
3. Constraint holds iff `Eval(assert, assert_env) == true`.

## Total Evaluation Rule

All constraints in bundle must hold before tx commit.

Violation relation:

`Violations = { c in Constraints | Holds(c) == false }`

Commit precondition:

`Violations == empty`
