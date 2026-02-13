# Canonical Execution Ledger Policy

## Source of Truth

- `ROADMAP.md` is the single canonical execution ledger.
- Canonical hierarchy is strict and linear:
  - Phase
  - Milestone
  - Checkbox

All execution status is authoritative only in `ROADMAP.md`.

## ID Model

- Phase section IDs: `AA`, `AB`, `AC`, ...
- Milestone IDs: `<PhaseCode><MilestoneNumber>` (example: `AC3`)
- Checkbox IDs: `<MilestoneID>.<ItemNumber>` (example: `AC3.2`)

Derived phase view IDs:
- `P<phase>.<milestone>.<item>` (example: `P12.3.2`)

## Derived Views

- `PHASE*.md` files are derived execution views for readability.
- They must not introduce independent status truth.
- Status values in `PHASE*.md` must match `ROADMAP.md` for mapped checkboxes.
- Planning/navigation docs (`PHASE_LEVEL_ROADMAP.md`, `JOURNEY_VECTOR.md`)
  are explicitly non-status and must not contain markdown checkboxes.

## One Checkbox = One Commit

For a checkbox marked done in `ROADMAP.md`:
- exactly one atomic commit should represent completion,
- commit message must include the checkbox ID token (example: `phase12 ac3.2`).

## Enforcement Scripts

- `scripts/check_roadmap_integrity.sh`
  - validates phase/milestone/checkbox structure and linear phase numbering.
- `scripts/check_phase_views_sync.sh`
  - validates status parity between `ROADMAP.md` and `PHASE*.md` views.
- `scripts/check_checkbox_commit_evidence.sh`
  - validates that checked checkboxes have corresponding commit evidence.
- `scripts/check_workflow_single_source.sh`
  - validates that non-canonical planning/navigation docs do not carry status checkboxes.
- `scripts/check_category_model_conformance.sh`
  - validates `docs/foundations/category-model.md` obligations against theorem/doc/artifact evidence.
- `scripts/check_canonical_execution_model.sh`
  - runs all canonical ledger checks.
