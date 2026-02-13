# Status Source Migration Plan

Current mode:
- `ROADMAP.md` is canonical execution status truth.
- `control-plane/execution/execution-ledger.yaml` is structural/planning metadata.

Target mode:
- `control-plane/execution/execution-ledger.yaml` becomes canonical status source.
- `ROADMAP.md` becomes generated execution view.

## Preconditions

1. Generator parity:
- deterministic round-trip between ledger model and roadmap markdown.

2. Gate parity:
- existing canonical execution checks can consume generated roadmap without weakening guarantees.

3. Commit-evidence continuity:
- checkbox token expectations stay stable across source migration.

## Cutover Steps

1. Introduce roadmap generator with stable ID mapping.
2. Add dual-source verification gate (ledger->roadmap and roadmap->ledger parity).
3. Freeze manual roadmap edits; enforce generated-only updates.
4. Switch `status_source_mode` to `execution_ledger_yaml_canonical`.
5. Keep compatibility window where `ROADMAP.md` is generated and reviewed.

## Rollback

If migration causes instability:
- revert `status_source_mode` to `roadmap_md_canonical`,
- disable generated-roadmap enforcement,
- preserve control-plane models as planning-only artifacts.
