# Formal Definition: Migration Correctness

Let:

- `M_v->v+1` be migration transform on history
- `R_v` replay under version `v`
- `R_v+1` replay under version `v+1`
- `StateMap_v->v+1` map old terminal state labels to new labels

Correctness requires commuting relation:

`R_v+1(M_v->v+1(H_v)) == StateMap_v->v+1(R_v(H_v))`

subject to representational equivalence of attrs/shadows.

## Conditions

1. Totality: every source event/state must have a defined mapping.
2. Executability: migrated history can be replayed under target IR.
3. Invariant preservation: all target constraints hold after migrated replay.

Cutover is valid iff all conditions hold and replay verification succeeds.
