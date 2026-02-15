# ADR-002: Bundle Registry Immutable Storage

## Status
Accepted

## Context
Deploying socio-technical systems requires deterministic execution across environments. We need a way to distribute compiled Core IR bundles that guarantees what was tested is what is running.

## Decision
We implement a content-addressed Bundle Registry.
1. Bundles are identified by the SHA-256 hash of their contents.
2. The storage layer (R2/KV) is append-only for blobs. A hash never points to different content.
3. Tenants reference bundles by hash, or by a specific version (SemVer) which Resolve to a hash.

## Consequences
- **Pros**: Immutable deployments; trivial rollback (just point to old hash); auditability.
- **Cons**: Requires garbage collection for unreferenced bundles; bundle size must be managed to keep registry performant.
