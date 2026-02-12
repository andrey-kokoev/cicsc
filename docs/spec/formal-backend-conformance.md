# Formal Definition: Backend Conformance

Given Core IR `IR`, backend `B`, and oracle interpreter `O`:

For every supported query/constraint/reducer execution context `x`:

`Eval_B(IR, x) == Eval_O(IR, x)`

Where equality means:

- identical boolean results for constraints
- row-set equivalence (order-insensitive unless ordered query) for views/queries
- equivalent state transition outputs for reducer replay

## Conformance Requirements

1. Unsupported constructs must be rejected at compile/typecheck time.
2. Supported constructs must match oracle semantics exactly.
3. Differential tests must exercise every lowered operator class.

Backend is conformant iff all required differential tests pass.
