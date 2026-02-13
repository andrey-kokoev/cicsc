# Tenant -> Bundle Binding Lifecycle (Pilot)

## State Model

A tenant binding is:

- `tenant_id`
- `bundle_id`
- `bundle_hash`
- `active_version`
- `updated_ts`

Audit trail (append-only):

- `audit_id` (monotonic)
- `tenant_id`
- `prev_bundle_hash`, `prev_active_version` (nullable for first bind)
- `next_bundle_hash`, `next_active_version`
- `changed_ts`

## Operations

### Bind

- Input: `(tenant_id, bundle_id, bundle_hash, active_version)`
- Semantics: upsert binding record.
- Idempotency: repeated bind with same tuple is no-op.

### Rebind (Upgrade/Downgrade)

- Input: same shape with new `(bundle_hash, active_version)`.
- Semantics: atomic update after verification gate passes.
- Idempotency: repeated rebind to same target is no-op.
- Audit: every bind/rebind appends one immutable audit row.

### Read Binding

- Returns current active tuple for tenant.

### Read Audit

- Returns ordered append-only history for tenant binding transitions.

## Guard Conditions

- Reject bind/rebind if bundle hash not present in registry.
- Reject install/load if stored bundle bytes re-hash to a value different from bound `bundle_hash`.
- Reject rebind if verification artifact is missing or failing.
- Require explicit migration authorization token for install/cutover paths.
- Reject requests without explicit `tenant_id`.
