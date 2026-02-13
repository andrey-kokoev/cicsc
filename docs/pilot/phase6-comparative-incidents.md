# Phase 6 Comparative Incident Register (Ticketing vs CRM)

Source artifact:
- `docs/pilot/phase6-comparative-incidents.json`

## Incident Set

| ID | Category | Severity | Recurrence | Observed In | Summary |
|---|---|---|---|---|---|
| CINC-CONFORMANCE-001 | conformance_gate | high | cross_vertical | ticketing, crm | Dual-backend required conformance gates remain shared deployment blockers. |
| CINC-SPEC-USABILITY-001 | dsl_usability | medium | single_vertical | crm | CRM grouped-view authoring required explicit `attrs_json` field extraction to satisfy typed row-field policy. |
| CINC-MIGRATION-001 | migration_ops | medium | cross_vertical | ticketing, crm | Migration preflight/dry-run/cutover controls are mandatory in both staged workloads. |

This register is the evidence artifact for `P6.1.3` / `W1.3`.
