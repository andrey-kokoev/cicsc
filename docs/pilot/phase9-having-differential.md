# Phase 9 HAVING Differential

Artifact:
- `docs/pilot/phase9-having-differential.json`

This report captures execution-vs-oracle differential checks for the newly
enabled `HAVING` construct across SQLite and Postgres lowerers.

Current status:
- SQLite differential is required and green.
- Postgres differential is tracked with deferred status due pg-mem planner
  limitations for HAVING (carried into Z2 parity hardening).
