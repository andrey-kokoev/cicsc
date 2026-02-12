# Pilot Runbook

## 1. Install

1. Compile and typecheck bundle/spec.
2. Install schema for tenant.
3. Bind tenant to active bundle/version.
4. Run baseline verification (`verify`) before opening traffic.

## 2. Upgrade

1. Freeze writes for target tenant window.
2. Compile/typecheck next bundle.
3. Run migration transform and replay verification in dry-run.
4. Activate next version only if verification artifact is clean.
5. Unfreeze writes.

## 3. Rollback

1. Freeze writes.
2. Rebind tenant to previous known-good version.
3. Re-run verification against previous version.
4. Unfreeze only after invariant checks pass.

## 4. Verify Loop

- Run verify after each deployment and scheduled intervals.
- Record report with tenant/version/timestamp.
- Escalate any violation as deployment blocker.

## 5. Incident Path

- Capture failing command payload + tenant context.
- Capture verify report and active version stamp.
- Open roadmap checkbox for root-cause fix before re-enabling affected path.
