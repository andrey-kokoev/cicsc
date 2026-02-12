# Migration Cookbook (v0)

## Common Migration Recipes

## 1. Rename Event Type

- Add `event_transforms.old_event.emit_as = "new_event"`.
- Keep payload identity unless fields change.
- Ensure target reducer handles `new_event`.

## 2. Payload Field Rename

- Define `payload_map` with explicit Expr path mapping.
- Keep transform deterministic.

## 3. State Rename

- Add full `state_map` for all source states.
- Verify no state is left unmapped.

## 4. Split One Event Into Two (v0 note)

- Not supported as one-to-many in v0 transform shape.
- Model as one event + target reducer evolution.

## 5. Drop Legacy No-op Events

- Set `{ drop: true }` for the legacy event transform.
- Verify stream resequencing behavior in tests.

## 6. Cutover Procedure

1. Pause tenant writes.
2. Transform history to target version.
3. Run replay verification on migrated history.
4. Activate target version.
5. Resume writes.
