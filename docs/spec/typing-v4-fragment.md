# Typing v4 Fragment

This note documents the scoped expression fragment used by the Lean v4 typing
theorems (`TypingV4Fragment` in `lean/Cicsc/Core/Meta/Typecheck.lean`).

## Included

- Literals: `litBool`, `litInt`, `litString`, `litNull`
- Variables: all current `var` references
- Object ops: `get`, `has`
- Boolean ops: `not`, `and`, `or`
- Comparison ops: `eq`, `ne`, `lt`, `le`, `gt`, `ge`
- Arithmetic ops: `add`, `sub`, `mul`, `div`
- Control/data ops: `ifThenElse`, `coalesce`

## Excluded

- `call(fn, args)`

## Rationale

- `call` is excluded because kernel typing has no stable function-signature table
  yet; admitting it would weaken the proof boundary via ad-hoc assumptions.
- The remaining operators are kept because they already have executable
  evaluator/typechecker alignment in the Lean core and are sufficient for v4
  proof-bearing constraints and query predicates.
