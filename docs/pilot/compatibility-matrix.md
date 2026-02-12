# Compatibility Matrix (Pilot)

| Bundle Spec/Core IR | Runtime Surface | Adapter | Status |
|---|---|---|---|
| v1 ticketing bundle | v1.5 coherent kernel + current runtime | sqlite/d1 | supported |
| v1 ticketing bundle | v1.5 coherent kernel + current runtime | postgres | conditional (dependency/bootstrap + conformance gate required) |
| pre-v1 bundles | current runtime | sqlite/d1 | migration required |
| unknown future bundles | current runtime | any | rejected by typecheck/compat gate |

## Rules

- Activation requires explicit matrix-supported tuple.
- Unsupported tuple must fail before deployment/cutover.
- Matrix updates require conformance evidence.
