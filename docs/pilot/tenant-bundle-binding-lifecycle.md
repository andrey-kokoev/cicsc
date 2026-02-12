# Tenant -> Bundle Binding Lifecycle (Pilot)

## State Model

A tenant binding is:

- `tenant_id`
- `bundle_id`
- `bundle_hash`
- `active_version`
- `updated_ts`

## Operations

### Bind

- Input: `(tenant_id, bundle_id, bundle_hash, active_version)`
- Semantics: upsert binding record.
- Idempotency: repeated bind with same tuple is no-op.

### Rebind (Upgrade/Downgrade)

- Input: same shape with new `(bundle_hash, active_version)`.
- Semantics: atomic update after verification gate passes.
- Idempotency: repeated rebind to same target is no-op.

### Read Binding

- Returns current active tuple for tenant.

## Guard Conditions

- Reject bind/rebind if bundle hash not present in registry.
- Reject rebind if verification artifact is missing or failing.
- Reject requests without explicit `tenant_id`.
