# CICSC Concurrency Model Contract (Phase 6)

Contract artifact:
- `docs/pilot/phase6-concurrency-contract.json`

## Supported Model

- Stream identity is `(tenantId, entityType, entityId)`.
- Guarantees are stream-scoped:
- append order is monotonic by `seq` within stream,
- replay applies only events in the same stream identity,
- same-stream write/write conflicts resolve as `abort-or-serialize`.

## Cross-Stream Boundaries

- No global total order is claimed across distinct streams.
- Cross-stream interleaving is allowed.
- Causality checks are scoped by declared stream identity.

## Explicit Non-Claims

- No distributed transaction guarantee.
- No backend lock-manager equivalence claim.
- No cross-tenant causality claim.

This contract defines the claim boundary for `P6.2.1` / `W2.1`.
