# Phase 9 SQL Feature Gates

Artifact:
- `docs/pilot/phase9-sql-feature-gates.json`

Phase 9 introduces explicit gates for deferred SQL candidates:
- `phase9.sql.having`
- `phase9.sql.exists`

Current status:
- `phase9.sql.having`: enabled, but only with mandatory execution-vs-oracle differential coverage.
- `phase9.sql.exists`: disabled; must fail fast at compile/lowering time.
