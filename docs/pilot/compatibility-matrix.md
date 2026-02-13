# Compatibility Matrix (Pilot)

| Bundle Spec/Core IR | Runtime Surface | Adapter | Status |
|---|---|---|---|
| v1 ticketing bundle | Lean v4 scoped kernel + Phase 6-gated runtime | sqlite/d1 | supported |
| v1 ticketing bundle | Lean v4 scoped kernel + Phase 6-gated runtime | postgres | conditional (required cross-backend + phase6 gates must be green) |
| v1 crm bundle | Lean v4 scoped kernel + Phase 6-gated runtime | sqlite/d1 | supported |
| v1 crm bundle | Lean v4 scoped kernel + Phase 6-gated runtime | postgres | conditional (required cross-backend + phase6 gates must be green) |
| pre-v1 bundles | current runtime | sqlite/d1 | migration required |
| unknown future bundles | current runtime | any | rejected by typecheck/compat gate |

## Rules

- Activation requires explicit matrix-supported tuple.
- Unsupported tuple must fail before deployment/cutover.
- Matrix updates require conformance evidence.
- Conditional postgres rows require:
  - `docs/pilot/phase6-required-gates.json` overall `pass`
  - `docs/pilot/phase6-concurrency-conformance.json` overall `pass`
