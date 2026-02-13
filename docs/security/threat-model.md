# Threat Model (v0)

## Assets

- Event history integrity.
- Snapshot/state integrity.
- Tenant-to-bundle binding correctness.
- Policy and authorization correctness.

## Trust Boundaries

- Client -> runtime HTTP API.
- Runtime -> storage adapter.
- Compiler outputs -> runtime install/bind path.

## Primary Threats

- Unauthorized command execution.
- Cross-tenant data access.
- History tampering or replay divergence.
- Partial/unsafe migration cutover.
- Silent policy drift.

## Mitigations

- Per-command authorization guard mapping (`auth_ok`).
- Tenant-scoped storage keys and routing.
- Replay verification before cutover.
- Version-stamped verify reports + invariant drift detection.
- Optional cryptographic hashing of history/snapshots.

## Residual Risks

- Misconfigured intrinsics can weaken policy guarantees.
- Incomplete adapter conformance can diverge backend semantics.
- Operational bypass of pause/migrate/resume protocol.

## Required Operational Controls

- Token protection for bundle/bind/migration admin endpoints (`BUNDLE_CREATE_TOKEN`, `TENANT_BIND_TOKEN`, `TENANT_MIGRATE_TOKEN`).
- Audit exports retained for policy and migration operations.
- Regular full-tenant verification runs.
