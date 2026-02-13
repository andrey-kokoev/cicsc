# CICSC Isolation and Concurrency Guarantees (Phase 7 Scoped)

This document states the current, evidence-backed isolation/concurrency surface
for Phase 7 and its explicit exclusion boundary.

## Normative Contract Artifact

- `docs/pilot/phase6-concurrency-contract.json`
- `docs/spec/concurrency-model-contract.md`
- `docs/pilot/phase7-concurrency-contract-delta.json`
- `docs/spec/concurrency-model-contract-phase7.md`

The supported model is `stream_serializable_with_scoped_cross_stream_behavior`.
Stream identity is `(tenantId, entityType, entityId)`.

## Formal Artifacts

- `lean/Cicsc/Core/Semantics/Isolation.lean`
- `lean/Cicsc/Core/Semantics/CausalityReplay.lean`

Key theorems currently available:
- `snapshot_no_dirty_reads`
- `writeWrite_conflict_abort_or_serialize`
- `replay_stream_preserves_happensBefore_order`
- `replay_deterministic_on_causallyEquivalent_streams`

## Executable Evidence

- `docs/pilot/phase6-concurrency-conformance.json`
- `docs/pilot/phase6-migration-concurrency-drill.json`
- `docs/pilot/phase7-concurrency-adversarial.json`
- `docs/pilot/phase7-isolation-differential.json`
- `docs/pilot/phase7-conflict-matrix-expanded.json`
- `tests/concurrency/transaction-model.test.ts`
- `tests/concurrency/causality-replay.test.ts`
- `tests/oracle/replay-determinism-multistream.test.ts`
- `tests/oracle/migration-concurrency-drill.test.ts`

## Supported Guarantee Scope

- Per-stream append order is monotonic by `seq`.
- Replay consumes only events matching exact stream identity.
- Same-stream write/write conflict outcome is deterministic: abort-or-serialize.
- Cross-stream interleaving is allowed and does not imply a global total order.
- Pause/migrate/resume protocol rejects writes while paused and resumes on the
  migrated version.
- Adversarial multi-tenant replay suites are required evidence for current
  causality/isolation claims.
- Backend isolation differential checks are required evidence for declared
  stream-level invariants.
- Conflict outcome coverage includes explicit retry and boundary cases
  (cross-stream, cross-tenant, idempotency policy paths).

## Explicit Scoped Exclusions

- No distributed transaction guarantee.
- No full global serializability claim across distinct streams.
- No backend lock-manager equivalence claim.
- No cross-tenant causality claim.
