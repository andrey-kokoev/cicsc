# Spec Construct Deprecation Policy

## Lifecycle

1. `Active`
2. `Deprecated` (warning emitted)
3. `Removed` (compile/typecheck error)

## Timing

- Deprecation must be announced in one minor release before removal.
- Removal requires next major release.

## Requirements

- Provide replacement construct.
- Provide migration/desugaring guidance.
- Document impact on existing specs.
