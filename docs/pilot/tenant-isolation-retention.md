# Pilot Tenant Isolation and Retention Policy

## Isolation Model

- Data partition key: `tenant_id` is mandatory in all event/snapshot/query access paths.
- Verification and migration operations run per-tenant context.
- No cross-tenant joins or reads in pilot workflows.

## Access and Execution

- Tenant binding must be explicit before command/view execution.
- Command idempotency receipts are namespaced by `tenant_id`.
- Audit exports include `tenant_id` and active bundle/version metadata.

## Retention

- Event history is append-only during pilot window.
- Snapshot materializations are mutable projections only; history remains source of truth.
- Retention windows and compaction policies must be declared before activation.

## Deletion/Export

- Export path must produce per-tenant audit bundle.
- Any deletion workflow must be explicit, logged, and out-of-band from normal command path.

## Compliance Guardrails

- Any operation lacking tenant context is rejected.
- Any migration without tenant-scoped verification artifact is rejected.
