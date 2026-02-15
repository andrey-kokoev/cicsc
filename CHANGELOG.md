# Changelog

All notable changes to this project will be documented in this file.

## [1.0.0] - 2026-02-15

### Added
- **Surface DSL**: New indentation-based language for describing entities and constraints.
- **Bundle Registry**: R2 blobs and KV index for immutable bundle distribution.
- **Postgres Adapter**: Robust backend support with native JSONB and window functions.
- **Migration Engine**: Automated diffing and event replay for schema evolution.
- **Conformance Suite**: Cross-backend differential testing against Lean 4 oracle.

### Changed
- **Lean Kernel**: Upgraded to v4 with complete typing and WF bridges.
- **Control Plane**: Simplified collaboration model using direct `execution-ledger.yaml` state.
- **Lowering**: Optimized SQLite lowering for complex nested expressions.

### Fixed
- Fixed race condition in SQLite stream lock implementation.
- Corrected SemVer resolution logic in Bundle Registry.
- Improved error messaging for guard rejections in the runtime.
