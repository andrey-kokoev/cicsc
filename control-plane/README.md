# Control Plane

`control-plane/` contains machine-readable planning and execution models for CICSC.

## Purpose

Provide a single coherent model stack for:
- objectives (why),
- observable capabilities (what),
- execution sequencing and status (when/how),
- closure gates (how completion is validated).

## Model Ownership

- `objectives/objective-model.yaml`
  - Mission-level objectives and success criteria.
  - No execution status.

- `capabilities/capability-model.yaml`
  - Observable capability atoms and acceptance signals.
  - No execution status.

- `execution/execution-ledger.yaml`
  - Canonical phase/milestone/checkbox status model (future source of truth).
  - During bootstrap, `ROADMAP.md` remains canonical status truth.

- `gates/gate-model.yaml`
  - Required validation/gating contracts for milestones/phases.
  - No execution status.

## Current Canonical Rule

Until explicit migration is completed:
- `ROADMAP.md` is canonical status truth.
- `PHASE*.md` are derived status views.
- `control-plane/*` models are authoritative for structure and intent, not runtime status.

## Derivation Flow (Target)

1. Validate schemas and model cross-references.
2. Generate views into `control-plane/views/`.
3. Generate/verify canonical markdown artifacts (`ROADMAP.md`, phase views).
4. Run canonical execution gates.

## Validation Entry Points

- `control-plane/scripts/validate_objective_model.sh`
- `control-plane/scripts/validate_capability_model.sh`
- `control-plane/scripts/validate_execution_ledger_model.sh`
- `control-plane/scripts/validate_gate_model.sh`
- `control-plane/scripts/validate_cross_model.sh`
- `control-plane/scripts/validate_all.sh`
- `control-plane/scripts/generate_views.sh`

Sync gate:
- `scripts/check_control_plane_sync.sh`
  - validates models, regenerates control-plane views, and fails on generated-view drift.
- `scripts/check_roadmap_structure_sync.sh`
  - validates that `ROADMAP.md` phase headers match control-plane execution structure for non-planned phases.
- `scripts/check_status_source_mode.sh`
  - enforces bootstrap status source mode (`roadmap_md_canonical`) until explicit cutover.

## Status-Data Discipline

- Status checkboxes belong only to canonical execution ledger artifacts.
- Planning/navigation docs must remain non-status.

## Generated Artifact Convention

Generated files must be explicitly marked:

- filename suffix: `*.generated.*`
- text formats (`.md`, `.yaml`, `.mmd`, `.sh`, ...): include header markers:
  - `AUTO-GENERATED FILE. DO NOT EDIT.`
  - `Source: <path>`
  - `Generator: <path>`
- json formats: include metadata fields:
  - `\"_generated\": true`
  - `\"_source\": \"<path>\"`
  - `\"_generator\": \"<path>\"`

Policy enforcement:
- `scripts/check_generated_artifacts_policy.sh`

Generated views:
- `control-plane/views/phase-level-roadmap.generated.md`
- `control-plane/views/journey-vector.generated.md`
- `control-plane/views/roadmap-structure.generated.md`
