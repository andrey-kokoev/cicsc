# Adapter Conformance Checklist

Use this checklist when validating a backend adapter against CICSC semantics.

- [ ] Supports required Core IR version.
- [ ] Executes transactional append + snapshot update atomically.
- [ ] Preserves stream ordering by `(tenant, type, entity, seq)`.
- [ ] Implements schema generation contract for events/snapshots/SLA status.
- [ ] Lowers Query AST operators in supported subset.
- [ ] Lowers Expr AST operators in supported subset.
- [ ] Enforces unsupported lowering via compile/typecheck rejection.
- [ ] Passes SQL-vs-oracle conformance tests.
- [ ] Passes cross-backend gate (`./scripts/run_cross_backend_gate.sh`) for declared scope.
- [ ] Passes migration replay verification tests.
- [ ] Supports tenant version activation semantics.
- [ ] Exposes deterministic behavior under concurrency tests.
