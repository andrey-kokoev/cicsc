# Operator Command Set (Migration + Verification Cutover)

## Pre-Cutover

1. Baseline gate:
- `./scripts/phase3_baseline.sh`

2. Build/semantic checks:
- `cd lean && lake build`
- `./scripts/phase3_ci_target.sh`

## Cutover Flow

1. Freeze write traffic for tenant.
2. Run migration dry-run transform.
3. Run replay verification before activation.
4. Activate target bundle/version.
5. Re-run verify after activation.
6. Unfreeze traffic.

## Rollback Flow

1. Freeze writes.
2. Rebind tenant to previous bundle hash/version.
3. Verify replay + constraints.
4. Unfreeze only if verify passes.

## Mandatory Artifacts

- baseline report
- pre-cutover verify report
- post-cutover verify report
- active `(tenant_id, bundle_id, bundle_hash, version)` tuple
