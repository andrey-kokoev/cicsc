# Migration Operations Runbook (Phase 5)

This runbook defines operator-facing flow for migration preflight, dry-run,
cutover, and rollback on the currently supported subset.

## 1. Preconditions

- Source and target bundles validate.
- Target bundle contains migration id.
- Migration is forward (`from_version < to_version`).
- Source history passes integrity checks (no seq regressions/gaps).

Use CLI preflight:

```bash
node cli/cicsc.mjs migration-preflight \
  --from ./bundle.v0.json \
  --to ./bundle.v1.json \
  --events ./events.v0.json \
  --migration v0_to_v1
```

Expected: `ok: true` in JSON output.

## 2. Dry-Run with Artifact

Generate deterministic dry-run report artifact before cutover:

```bash
node cli/cicsc.mjs migration-dry-run \
  --from ./bundle.v0.json \
  --to ./bundle.v1.json \
  --events ./events.v0.json \
  --migration v0_to_v1 \
  --artifact ./artifacts/migration-dry-run.json
```

Expected artifact shape:
- `version: "cicsc/migration-dry-run-v1"`
- `ok`
- `source_events`
- `migrated_events`
- full `preflight` check breakdown

## 3. Cutover (Pause/Migrate/Activate/Resume)

Runtime cutover uses `cutoverPauseMigrateResume` and now records boundaries:
- `paused_at`
- `verified_at`
- `switched_at`
- `resumed_at`

Operational expectation:
1. pause tenant writes
2. verify migration replay
3. write migrated history
4. switch active version
5. resume tenant

## 4. Rollback (Reversible Subset)

Rollback is only supported when inverse can be constructed:
- no dropped events,
- no payload transforms,
- injective event mapping,
- injective state mapping.

CLI rollback:

```bash
node cli/cicsc.mjs migration-rollback \
  --to ./bundle.v1.json \
  --events ./events.v1.json \
  --migration v0_to_v1 \
  --out-events ./events.v0.rolledback.json
```

If rollback is unsafe, command returns non-zero with explicit error reason.

## 5. Failure Handling

- Any preflight failure: block cutover.
- Any dry-run failure: block cutover and capture artifact.
- Any rollback failure: preserve current history; do not partially mutate.
- Resume boundary must always execute even on failure paths.

