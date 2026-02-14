# Control Plane

`control-plane/` contains machine-readable planning and execution models for CICSC.

## Purpose

Provide a single coherent model stack for:
- objectives (why),
- observable capabilities (what),
- execution sequencing and status (when/how),
- closure gates (how completion is validated).

## Boundary to Genesis

`docs/genesis/*` is the conceptual prose domain.
`control-plane/*` is the mechanized contract domain.

Control-plane models are not replacements for genesis prose; they are structured
projections used for executable validation and gating.

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
  - Includes immutable message envelopes with append-only `message_events`, transition policy, rescind/supersede semantics, and evidence bindings (`commit` + `digest`).
  - Includes `worktree_governance` semantics (single owner per worktree, owner-dispatch authority, and worktree creation authority list).
  - Binds collaboration claims to objective/capability/ledger scope.
  - No execution status.
  - Canonical worktree processing entry point is mailbox projection:
    `control-plane/views/worktree-mailboxes.generated.json`.
  - `WORKTREE_ASSIGNMENT.md` files are disallowed for protocol execution.

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
- `control-plane/scripts/collab_validate.sh`
- `control-plane/scripts/validate_all.sh`
- `control-plane/scripts/generate_views.sh`
- `control-plane/scripts/collab_inbox.sh`
- `control-plane/scripts/collab_append_event.sh`
- `control-plane/scripts/collab_dispatch.sh`
- `control-plane/scripts/collab_create_assignment.sh`
- `control-plane/scripts/collab_delegate_worktree.sh`
- `control-plane/scripts/collab_help.sh`
- `control-plane/scripts/collab_claim_next.sh`
- `control-plane/scripts/collab_fulfill.sh`
- `control-plane/scripts/collab_close_ingested.sh`
- `control-plane/scripts/collab_show_assignment.sh`
- `control-plane/scripts/collab_status.sh`
- `control-plane/scripts/collab_dry_run.sh`
- `control-plane/scripts/collab_commit_views.sh`
- `control-plane/scripts/collab_run_once.sh`
- `control-plane/scripts/collab_stale_watch.sh`

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
- `control-plane/views/assignments.generated.json`
- `control-plane/views/worktree-mailboxes.generated.json`

## Worktree Agent Loop (Normative)

Execution location rule:
- run `control-plane/scripts/collab_*.sh` from repository root
  (`/home/andrey/src/cicsc`)
- select target worker context with `--worktree <path>`

For each execution worktree:
1. Read `control-plane/views/worktree-mailboxes.generated.json`.
2. Select inbox messages addressed to that worktree with actionable status
   (`queued` or `sent`).
3. Execute assignment scope on the bound branch.
4. Append immutable `message_events` with status transitions and evidence bindings.
5. Stop when no actionable inbox messages remain.

Quickstart helpers:
- worker flow: `./control-plane/scripts/collab_help.sh --role worker --worktree "$PWD"`
- main flow: `./control-plane/scripts/collab_help.sh --role main --worktree /home/andrey/src/cicsc`
- main batch dispatch: `./control-plane/scripts/collab_dispatch_batch.sh --agent-ref AGENT_KIMI --count 2`

## Multi-Assignment Worker Flow (End-to-End)

Example with two queued assignments for Kimi:

1. Inspect current lane state:
   - `./control-plane/scripts/collab_status.sh --worktree /home/andrey/src/cicsc/worktrees/kimi`
2. Claim next actionable message (acknowledged-first guard enforced):
   - `./control-plane/scripts/collab_claim_next.sh --worktree /home/andrey/src/cicsc/worktrees/kimi`
   - one-command claim+commit: `./control-plane/scripts/collab_claim_next.sh --worktree /home/andrey/src/cicsc/worktrees/kimi --commit`
3. Show obligation delta and next step:
   - `./control-plane/scripts/collab_show_assignment.sh --ref ASSIGN_...`
4. Pick likely evidence refs:
   - `./control-plane/scripts/collab_pick_evidence.sh --assignment-ref ASSIGN_...`
5. Fulfill with typed evidence bindings:
   - `./control-plane/scripts/collab_fulfill.sh --message-ref MSG_... --worktree /home/andrey/src/cicsc/worktrees/kimi --with scripts/check_canonical_execution_model.sh --auto-report --lazy --suggest-commit --auto-commit`
6. Main ingests and closes:
   - `./control-plane/scripts/collab_close_ingested.sh --message-ref MSG_... --commit <sha>`
7. Repeat until status is idle:
   - `./control-plane/scripts/collab_run_loop.sh --worktree /home/andrey/src/cicsc/worktrees/kimi --max-steps 20`
8. Optional homogeneous batch mode:
   - `./control-plane/scripts/collab_sweep.sh --worktree /home/andrey/src/cicsc/worktrees/kimi --script scripts/check_canonical_execution_model.sh --gate-report docs/pilot/category-model-conformance.json --lazy`
9. Optional diagnostics:
   - `./control-plane/scripts/collab_diff.sh --assignment-ref ASSIGN_...`
   - `./control-plane/scripts/collab_summary.sh --worktree /home/andrey/src/cicsc/worktrees/kimi --since 2026-02-13`
10. Optional fuzzy picker session (requires `fzf`):
   - `./control-plane/scripts/collab_fzf.sh --worktree /home/andrey/src/cicsc/worktrees/kimi`
