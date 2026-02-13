# Phase 5 Ticketing Incident Register

Source artifact:
- `docs/pilot/phase5-ticketing-incidents.json`

## Open Incidents

| ID | Category | Severity | Status | Summary |
|---|---|---|---|---|
| INC-PG-HARNESS-001 | missing_primitive | high | open | Postgres conformance gate cannot execute in current environment because `pg-mem` dependency is missing. |
| INC-ORDER-COLLATION-001 | drift_risk | medium | open | Backend default NULL/collation behavior differs and requires explicit policy-driven handling in cross-backend assertions. |
| INC-PERF-BASELINE-001 | perf_visibility | medium | open | Staged run currently records pass/fail only; no latency/throughput instrumentation baseline yet. |
