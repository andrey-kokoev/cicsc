# Status Source Migration Plan

Migration status: complete.

Current mode:
- `control-plane/execution/execution-ledger.yaml` is canonical status truth.

Steady-state rule:
- execution status edits happen only in `execution-ledger.yaml`.
- no compatibility alias is required.

## Achieved Conditions

1. Generator parity:
- deterministic generation from ledger model to execution views.

2. Gate parity:
- canonical execution checks consume ledger-native integrity, status, and phase-sync gates.

3. Commit-evidence continuity:
- checkbox token expectations remain `phase<no> <checkbox-id>`.
