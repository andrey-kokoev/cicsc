# Canonical Execution Ledger Policy

## Source of Truth

- `control-plane/execution/execution-ledger.yaml` is the single canonical execution ledger.
- Canonical hierarchy is strict and linear:
  - Phase
  - Milestone
  - Checkbox

All execution status is authoritative only in `control-plane/execution/execution-ledger.yaml`.

## ID Model

- Phase section IDs: `AA`, `AB`, `AC`, ...
- Milestone IDs: `<PhaseCode><MilestoneNumber>` (example: `AC3`)
- Checkbox IDs: `<MilestoneID>.<ItemNumber>` (example: `AC3.2`)

Derived phase view IDs:
- `P<phase>.<milestone>.<item>` (example: `P12.3.2`)

## Derived Views

- `PHASE*.md` files are derived execution views for readability.
- They must not introduce independent status truth.
- Status values in `PHASE*.md` must match `control-plane/execution/execution-ledger.yaml` for mapped checkboxes.
- Planning/navigation docs (`PHASE_LEVEL_ROADMAP.md`, `JOURNEY_VECTOR.md`)
  are explicitly non-status and must not contain markdown checkboxes.

Compatibility alias (temporary):
- `ROADMAP.md` is generated from `execution-ledger.yaml` for transition safety.
- It is non-canonical and must not be edited directly.

## One Checkbox = One Commit

For a checkbox marked done in `control-plane/execution/execution-ledger.yaml`:
- exactly one atomic commit should represent completion,
- commit message must include the checkbox ID token (example: `phase12 ac3.2`).

## Enforcement Scripts

- `scripts/check_execution_ledger_integrity.sh`
  - validates phase/milestone/checkbox structure and linear phase numbering.
- `scripts/check_phase_views_sync_ledger.sh`
  - validates status parity between `execution-ledger.yaml` and `PHASE*.md` views.
- `scripts/check_checkbox_commit_evidence_ledger.sh`
  - validates that checked checkboxes have corresponding commit evidence.
- `scripts/check_workflow_single_source.sh`
  - validates that non-canonical planning/navigation docs do not carry status checkboxes.
- `scripts/check_control_plane_sync.sh`
  - validates control-plane models and generated views remain synchronized.
- `scripts/check_execution_structure_sync.sh`
  - validates generated execution structure/index views against `execution-ledger.yaml`.
- `scripts/check_execution_structure_roundtrip_ledger.sh`
  - validates execution status projection coverage/parity for non-planned ledger scope.
- `scripts/check_roadmap_compat_alias_sync.sh`
  - validates generated `ROADMAP.md` compatibility alias remains in sync.
- `scripts/check_gate_model_roundtrip.sh`
  - validates canonical gate wrapper delegation and gate-order parity to gate-model.
- `scripts/check_status_source_mode.sh`
  - validates allowed status-source mode.
- `scripts/check_status_projection_sync.sh`
  - validates generated status projection parity with canonical ledger status.
- `scripts/check_generated_artifacts_policy.sh`
  - validates generated-artifact markers for `*.generated.*` files.
- `scripts/check_category_model_conformance.sh`
  - validates `docs/foundations/category-model.md` obligations against theorem/doc/artifact evidence.
- `scripts/check_canonical_execution_model.sh`
  - runs all canonical ledger checks.
