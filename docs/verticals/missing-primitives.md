# Missing Primitives Identified From Vertical Specs

After implementing CRM/Kanban/Ticketing vertical specs, the following primitive gaps were identified:

## 1. Event Transform Fan-out

- Current migration transform supports one-to-one event rewrite.
- Vertical evolution frequently needs one-to-many fan-out.

## 2. Native SLA Declaration in Spec DSL

- Vertical specs model SLA signals via shadows/commands.
- Need first-class Spec DSL `slas` section with compile-time validation.

## 3. Rich Aggregates in Views

- Pipeline metrics need derived rate/ratio convenience operators.
- Current Query AST can express these but lacks ergonomic DSL sugar.

## 4. Row-level Security Sugar

- Runtime supports `row_policy`, but Spec-level sugar for common owner/role patterns is missing.

## 5. Multi-entity Commands

- Real workflows need atomic cross-entity command intents.
- Current command model is single-entity stream scoped.
