# Semantic Versioning Policy

This policy applies to:

- Spec DSL
- Core IR
- Runtime/API
- Kernel API

## Rules

- `MAJOR`: breaking semantic or grammar change.
- `MINOR`: backward-compatible feature additions.
- `PATCH`: backward-compatible fixes/docs/tests only.

## Cross-Layer Requirement

A Core IR major bump requires:

1. Updated compatibility matrix.
2. Migration guidance.
3. Adapter conformance update.
