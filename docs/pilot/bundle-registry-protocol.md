# Bundle Registry Protocol (Pilot Minimum)

## Identifier Model

- `bundle_id`: stable logical name
- `bundle_hash`: immutable content hash
- `ir_version`: bundle-declared IR/runtime compatibility marker

## Operations

- `PUT /bundles/:bundle_id/:bundle_hash`
  - Stores immutable bundle content and metadata.
- `GET /bundles/:bundle_id/:bundle_hash`
  - Retrieves exact immutable bundle.
- `GET /bundles/:bundle_id/latest`
  - Returns latest approved hash pointer.

## Constraints

- Immutable content addressability by `bundle_hash`.
- No in-place mutation for existing hash.
- Metadata must include compile/typecheck status stamp.

## Reference Contract

- Storage backend can vary (R2/KV/local), protocol shape stays stable.
- Runtime consumes only `(bundle_id, bundle_hash)` references, not mutable names.
