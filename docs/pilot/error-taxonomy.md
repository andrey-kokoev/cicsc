# Pilot Error Taxonomy

## Format

All pilot-surface errors should follow:

- `code`: stable machine-readable token
- `path`: qualified location (`layer.segment.field`)
- `message`: operator-readable summary
- `action`: immediate remediation guidance

## Categories

### Compile/Typecheck

- `SPEC_TYPECHECK_FAILED`
- `IR_TYPECHECK_FAILED`
- `LOWERING_UNSUPPORTED`

### Runtime/Execution

- `TX_CONSTRAINT_VIOLATION`
- `TX_AUTH_REJECTED`
- `TX_IDEMPOTENCY_CONFLICT`
- `TENANT_NOT_BOUND`

### Verification/Migration

- `VERIFY_FAILED`
- `MIGRATION_TRANSFORM_REJECTED`
- `MIGRATION_REPLAY_MISMATCH`
- `CUTOVER_BLOCKED`

### Ops/Infrastructure

- `BUNDLE_LOAD_FAILED`
- `SCHEMA_APPLY_FAILED`
- `ADAPTER_DEPENDENCY_MISSING`

## Rules

- No string-only ad hoc errors on pilot paths.
- No silent fallback on semantic failures.
- Path must identify source layer (`spec`, `core.ir`, `runtime`, `migration`, `adapter`).
