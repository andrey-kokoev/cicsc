# Phase 9 SQL Feature Gates

Artifact:
- `docs/pilot/phase9-sql-feature-gates.json`

Phase 9 introduces explicit gates for deferred SQL candidates:
- `phase9.sql.having`
- `phase9.sql.exists`

Both are currently disabled and must fail fast at compile/lowering time until
operator-specific oracle differential coverage is added.
