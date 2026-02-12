# Versioning and Compatibility Rules

## Version Domains

- `Spec DSL version`
- `Core IR version`
- `Runtime API version`
- `Kernel API version`

## Compatibility Policy

1. Spec DSL minor additions must compile to same Core IR major.
2. Core IR major bump indicates grammar/semantic break.
3. Runtime/API changes must preserve prior minor behavior unless major bump.
4. Kernel API must follow semver with explicit stability guarantees.

## Migration Requirements

- Upgrading Spec version requires total migration path for persisted histories.
- Version skips are disallowed unless explicit multi-hop migration chain exists.

## Adapter Requirements

- Adapter must declare supported Core IR major/minor range.
- Compilation fails if target adapter does not support bundle IR version.

## Cutover Rule

Tenant active version may change only after successful replay verification for target version.
