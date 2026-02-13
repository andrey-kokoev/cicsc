# CICSC Proven vs Experimental Feature Gates (Phase 6)

Gate registry:
- `docs/pilot/phase6-feature-gates.json`

## Proven Surface

- compile/install/verify CLI + API path
- migration preflight/dry-run/rollback flow
- required and cross-backend conformance gates
- phase6 concurrency and migration drill gates

## Experimental Surface

- cross-stream merge conflict resolution
- distributed transaction orchestration
- automatic migration synthesis
- backend lock-manager equivalence claims

Only `proven` items are eligible for operator defaults and normative guarantees.
