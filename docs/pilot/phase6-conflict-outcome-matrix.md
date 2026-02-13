# Phase 6 Deterministic Conflict Outcome Matrix

Matrix artifact:
- `docs/pilot/phase6-conflict-outcome-matrix.json`

## Cases

- `same_stream_write_write`: deterministic outcome is `abort_or_serialize`.
- `retry_after_conflict`: deterministic outcome is `retry_with_fresh_tx`.
- `merge_conflicting_writes`: deterministic outcome is `reject_not_supported`.

This artifact closes `P6.2.3` / `W2.3` with explicit per-case outcomes and evidence links.
