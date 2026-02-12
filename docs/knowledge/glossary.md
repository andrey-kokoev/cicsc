# CICSC Glossary

- **Spec DSL**: User-intent language layer compiled into Core IR.
- **Core IR**: Backend-agnostic semantic representation.
- **Reducer Fold**: Deterministic replay of events into snapshot state.
- **Snapshot Constraint**: Per-row invariant over replayed snapshots.
- **Bool Query Constraint**: Global/cardinality invariant over query results.
- **Conformance**: Equivalence of backend execution to oracle semantics.
- **Migration Edge**: Total transform from version `N` to `N+1`.
- **Replay Verification**: Recompute state/invariants from history and validate.
- **Cutover**: Activation switch to new version after successful verification.
- **Kernel**: Dependency-minimal semantic core package.
