# Core Calculus Semantics Reference (v0)

## Expr

- `lit`: constant value.
- `var`: environment lookup (`state`, `actor`, `input`, `attrs`, `row`, `arg`, event vars).
- `get` / `has`: JSON path access predicates.
- Boolean operators: `not`, `and`, `or`, `bool`.
- Relational operators: `eq`, `ne`, `lt`, `le`, `gt`, `ge`, `in`.
- Numeric operators: `add`, `sub`, `mul`, `div`.
- Control/value operators: `if`, `coalesce`, `is_null`.
- Domain operators: `time_between`, `map_enum`, intrinsic `call`.

Evaluation is pure and deterministic for deterministic intrinsics.

## Query

- Source forms: `snap`, `sla_status`, `join`.
- Pipeline operators: `filter`, `project`, `group_by`, `order_by`, `limit`, `offset`.

Query semantics are relational transformations over finite rows.

## Reducer

- `set_state(expr)`: updates entity state.
- `set_attr(name, expr)`: writes declared attribute.
- `clear_attr(name)`: removes optional attr.
- `set_shadow(name, expr)`: writes materialized shadow.

Reducers are ordered folds over event streams.

## Constraints

- `snapshot`: boolean Expr over each replayed row.
- `bool_query`: query result cardinality/assertion over relational output.

## Runtime Invariant

Committed state is only the replay/reducer image of committed history.
