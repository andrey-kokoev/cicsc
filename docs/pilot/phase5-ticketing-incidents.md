# Phase 5 Ticketing Incident Register

Source artifact:
- `docs/pilot/phase5-ticketing-incidents.json`

## Open Incidents

| ID | Category | Severity | Status | Summary |
|---|---|---|---|---|
| INC-PG-HARNESS-001 | missing_primitive | high | resolved | Postgres conformance gate executes after `pg-mem` dependency + harness/lowering alignment fixes. |
| INC-ORDER-COLLATION-001 | drift_risk | medium | resolved | Lowering now emits explicit NULL ordering clauses; collation behavior remains explicitly policy-scoped in conformance contract. |
| INC-PERF-BASELINE-001 | perf_visibility | medium | resolved | Staged run now records per-check durations, thresholds, and aggregate checks-per-minute metrics. |
