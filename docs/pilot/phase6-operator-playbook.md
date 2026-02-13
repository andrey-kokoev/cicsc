# Phase 6 Operator Playbook: Multi-Tenant Rollout / Rollback / Incident Triage

## Scope

This playbook applies to tenant-scoped bundle deployment and migration operations.

## Rollout (Per Tenant)

1. Run conformance gate: `node cli/cicsc.mjs gates --suite cross-backend`.
2. Run concurrency gate: `node cli/cicsc.mjs gates --suite phase6-concurrency`.
3. Run migration preflight + dry-run against tenant stream set.
4. Bind tenant to target bundle/version.
5. Execute verify on tenant after activation.
6. Record artifact set in `docs/pilot/`.

## Rollback (Per Tenant)

1. Pause tenant write traffic.
2. Run rollback transform for declared migration chain.
3. Rebind tenant to prior bundle/version.
4. Execute verify and replay checks.
5. Resume writes only on green verification.

## Incident Triage

Severity policy:
- `critical`: invariant violation, failed verify, or replay divergence.
- `high`: conformance gate fail on required matrix.
- `medium`: migration drill failure or degraded operational SLO.
- `low`: non-blocking diagnostics.

Triage sequence:
1. Classify severity and impacted tenants.
2. Freeze affected tenant writes for `critical`/`high`.
3. Capture logs/artifacts from gates and migration drill.
4. Decide rollback or hotfix path.
5. File explicit execution-ledger item for unresolved root cause.

## Required Artifacts

- `docs/pilot/phase6-concurrency-conformance.json`
- `docs/pilot/phase6-migration-concurrency-drill.json`
- tenant binding audit evidence
- pre/post verify reports

This playbook is the operator baseline for `P6.3.3` / `W3.3`.
