# Troubleshooting Guide

This guide helps diagnose and resolve common issues encountered while using or developing for CICSC.

## Common CLI Issues

### `Command failed: ./control-plane/complete.sh`
- **Cause**: Gate checks failed.
- **Solution**: Run `./control-plane/check_gates.sh` manually to see which script is failing. Common failures include linting errors, missing commit evidence, or Ledger integrity violations.

### `ERROR: Execution ledger out of sync with phase views`
- **Cause**: You updated `control-plane/execution-ledger.yaml` but didn't run the sync script.
- **Solution**: Run `./control-plane/validate.sh`. It should automatically sync the Phase MD files or tell you which ones are broken.

---

## Runtime / API Issues

### `400 Bad Request: guard rejected`
- **Cause**: The `when` or `auth` clause in your Spec rejected the command.
- **Solution**: Check the command input against the entity state. If you have shadows, ensure they were populated correctly by previous events.

### `500 Internal Server Error: Dialect error`
- **Cause**: SQL lowering failed for the chosen backend (SQLite/Postgres).
- **Solution**: Check `runtime/db/` logs. Ensure you are using the correct adapter for your database. Verify if the failing expression is within the supported subset for that backend (see `feature-parity-matrix.md`).

---

## Migration Issues

### `Breaking change detected: migration required`
- **Cause**: You modified an entity schema (e.g., removed a field, changed a type) in a way that is not backward compatible.
- **Solution**: Use `scripts/generate_migration.mjs` to create a transformation plan. Run a `dry-run` to verify event mapping before applying to production.

### `Migration verification failed: Invariant breach`
- **Cause**: After replaying events in the new schema, a global constraint was violated.
- **Solution**: Re-evaluate your transformation logic. Ensure that mandatory new fields are populated with sensible defaults that satisfy existing invariants.
