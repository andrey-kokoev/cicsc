# Phase 3 Exit Checklist

## Pass/Fail Criteria

Pass requires all of the following:

- Baseline gate is green (`./scripts/phase3_baseline.sh`).
- CI target is green (`./scripts/phase3_ci_target.sh`).
- Automation entrypoint uses `./scripts/ci.sh` (which delegates to `phase3_ci_target.sh`).
- No unresolved high-severity semantic bugs in pilot findings.
- Forced follow-up execution-ledger section `T` has no open critical items.
- Pilot artifacts exist:
  - scope contract
  - runbook
  - findings report
  - compatibility matrix

Fail if any criterion above is unmet.
