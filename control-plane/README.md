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

- `collaboration/collab-model.yaml`
  - Typed agent collaboration contract (claims, obligations, evidence, handoff protocol).
  - Includes executable task assignments (`assignments`) binding agent/worktree/branch to ledger checkbox scope.
  - Binds collaboration claims to objective/capability/ledger scope.
  - No execution status.

- `execution/execution-ledger.yaml`
  - Canonical phase/milestone/checkbox status model.

- `gates/gate-model.yaml`
  - Required validation/gating contracts for milestones/phases.
  - No execution status.

## Current Canonical Rule

Current mode (`status_source_mode: execution_ledger_yaml_canonical`):
- `control-plane/execution/execution-ledger.yaml` is canonical status truth.
- `PHASE*.md` remain derived status views.
- `control-plane/*` models are authoritative for structure, status (modeled scope), and gating intent.

## Derivation Flow

1. Validate schemas and model cross-references.
2. Generate views into `control-plane/views/`.
3. Run canonical execution gates.

## Validation Entry Points

- `control-plane/scripts/validate_objective_model.sh`
- `control-plane/scripts/validate_capability_model.sh`
- `control-plane/scripts/validate_execution_ledger_model.sh`
- `control-plane/scripts/validate_gate_model.sh`
- `control-plane/scripts/validate_collab_model.sh`
- `control-plane/scripts/validate_cross_model.sh`
- `control-plane/scripts/validate_all.sh`
- `control-plane/scripts/generate_views.sh`

Sync gate:
- `scripts/check_control_plane_sync.sh`
  - validates models, regenerates control-plane views, and fails on generated-view drift.
- `scripts/check_execution_structure_sync.sh`
  - validates generated execution structure/index views against execution-ledger.
- `scripts/check_execution_structure_roundtrip_ledger.sh`
  - validates execution status projection parity against execution-ledger non-planned scope.
- `scripts/check_gate_model_roundtrip.sh`
  - validates canonical gate wrapper delegation and gate-order generation parity.
- `scripts/check_status_source_mode.sh`
  - validates allowed status source mode values.
- `scripts/check_status_projection_sync.sh`
  - validates execution status projection coverage for execution-ledger non-planned checkbox scope.

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
  - `"_generated": true`
  - `"_source": "<path>"`
  - `"_generator": "<path>"`

Policy enforcement:
- `scripts/check_generated_artifacts_policy.sh`

Generated views:
- `control-plane/views/phase-level-roadmap.generated.md`
- `control-plane/views/journey-vector.generated.md`
- `control-plane/views/execution-structure.generated.md`
- `control-plane/views/phase-index.generated.json`
- `control-plane/views/gate-order.generated.json`
- `control-plane/views/execution-status.generated.json`
