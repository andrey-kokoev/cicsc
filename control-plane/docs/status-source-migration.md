# Status Source Migration Plan

Migration status: complete.

Current mode:
- `control-plane/execution/execution-ledger.yaml` is canonical status truth for roadmap phase scope.
- `ROADMAP.md` is generated compatibility alias for the same scope.

Steady-state rule:
- execution status edits happen only in `execution-ledger.yaml`.
- roadmap markdown is generated, never authored.

## Achieved Conditions

1. Generator parity:
- deterministic generation from ledger model to roadmap compatibility markdown.

2. Gate parity:
- canonical execution checks consume ledger-native integrity, status, and phase-sync gates.

3. Commit-evidence continuity:
- checkbox token expectations remain `phase<no> <checkbox-id>`.

## Transition Safety Window

Compatibility alias is retained while downstream scripts/docs are migrated:
- `ROADMAP.md` (generated)
- `control-plane/views/roadmap-status.generated.json` (generated alias)

## Rollback

If migration causes instability:
- keep `status_source_mode` set to `execution_ledger_yaml_canonical`,
- temporarily bypass compatibility-alias sync gate,
- preserve execution-ledger as canonical source of truth.
