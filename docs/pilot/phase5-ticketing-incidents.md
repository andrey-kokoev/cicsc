# Phase 5 Ticketing Incident Register

Source artifact:
- `docs/pilot/phase5-ticketing-incidents.json`

## Open Incidents

| ID | Category | Severity | Status | Summary |
|---|---|---|---|---|
| INC-PG-HARNESS-001 | missing_primitive | high | resolved | Postgres conformance gate executes after `pg-mem` dependency + harness/lowering alignment fixes. |
| INC-ORDER-COLLATION-001 | drift_risk | medium | open | Backend default NULL/collation behavior differs and requires explicit policy-driven handling in cross-backend assertions. |
| INC-PERF-BASELINE-001 | perf_visibility | medium | resolved | Staged run now records per-check durations, thresholds, and aggregate checks-per-minute metrics. |
