# Runtime Kernel — Reference Implementation Guide (Informative)

## 0. Status

This document describes a reference implementation approach for the CICSC runtime kernel.

This document is informative. Normative semantics are defined by Core IR v0 and the Target Adapter Interface.

---

## 1. Runtime Responsibilities

A CICSC runtime MUST:

1. validate Core IR bundle (schema + type checks)
2. accept commands and enforce idempotency
3. load snapshots
4. evaluate guards (VM + constraints)
5. append events atomically
6. apply reducers to update snapshots
7. update SLA state
8. serve views
9. support replay verification for migrations

---

## 2. Data Model (Logical)

Runtime logic depends on the following logical objects:

- Event: `{tenant, entity_type, entity_id, seq, event_type, payload, ts, actor}`
- Snapshot: `{tenant, entity_type, entity_id, state, attrs, shadows, updated_ts}`
- Receipt: `{tenant, command_id, entity_type, entity_id, result_hash, ts}`

Adapters map these to physical schemas.

---

## 3. Command Execution Algorithm

### 3.1 Inputs

- `tenant_id`
- `actor_id`
- `command_id` (idempotency key)
- `entity_type`
- `entity_id` (optional for create)
- `cmd_name`
- `input_json`

### 3.2 Steps (single transaction)

1. **Idempotency**
   - if receipt exists for `(tenant, command_id)`, return stored result.

2. **Resolve entity id**
   - if entity_id absent and command is `create`, generate stable id.

3. **Load snapshot**
   - `snap := adapter.get_snapshot(...)` else synthesize empty snapshot.

4. **Evaluate guard**
   - Build VM env:
     - `$now`, `$actor`, `$state`, `$attrs`, `$input`
   - Evaluate `guard.expr` in VM.
   - VM resolves `call.constraint(...)` by delegating to adapter `eval_constraint(...)`.
   - If guard false: abort with error.

5. **Emit events**
   - For each `EventSpec`:
     - evaluate payload Expr nodes to JSON object
     - form event batch with consistent timestamp (`$now`) and actor.

6. **Append events**
   - `adapter.append_events(...)` with batch and command_id

7. **Apply reducers**
   - For each appended event:
     - apply reducer ops (set_state/set_attr/clear_attr/set_shadow)
   - Write snapshot:
     - `adapter.put_snapshot(...)`

8. **SLA update**
   - For each appended event:
     - `adapter.sla_apply_event(...)`

9. **Write receipt**
   - Store deterministic result summary (entity_id + event seq range).

10. **Commit**
   - End transaction.

---

## 4. VM Implementation Notes

### 4.1 Totality

The VM MUST be total:
- unsupported ops or type errors MUST yield `null` (or false under explicit `bool` coercion) as specified by Core IR.
- runtime MUST reject ill-typed IR at load time to avoid ambiguous runtime behavior.

### 4.2 Node Execution

Implement Expr evaluation as a pure function:

```
eval_expr(expr, env) -> Value
```

Where `env` provides typed bindings for:

- now
- actor
- state
- input fields
- attrs fields
- row fields (view/constraint context)
- arg fields (constraint/view parameters)

### 4.3 Intrinsics

Implement the closed intrinsic set:

- has_role(actor, role)
- role_of(actor)
- auth_ok(actor, cmdref)
- constraint(name, args)
- allowed(...) (policy call; treated as `call` into policy env)
- len/str/int/float (strict coercions)

---

## 5. View Execution

### 5.1 Strategy

Views are executed via adapter:

- `exec_view_query(tenant, view_id, params)`

Runtime MUST NOT implement backend-specific querying.

### 5.2 Post-processing

If adapter declares limited ordering, runtime MAY post-sort rows deterministically using Expr evaluation on row bindings.

This post-sort behavior MUST be explicit in bundle metadata.

---

## 6. SLA Enforcement

If adapter supports cron:

- adapter is responsible for scheduled breach checks and enforcement emissions.

If adapter lacks scheduler:

- runtime MUST expose an endpoint that executes `sla_check_due` and applies enforcement.

Enforcement MUST be implemented as event emission on the affected entity stream.

---

## 7. Replay Verification

Replay verification is used for upgrades:

1. Materialize migrated history into new versioned storage.
2. Rebuild snapshots by replaying reducers.
3. Re-evaluate all constraints and SLAs over replayed history.
4. Reject on any violation.

Runtime SHOULD expose:

- `verify_migration(from_version,to_version) -> report`

---

## 8. Error Model

Runtime errors are classified:

- `SpecError` (invalid bundle)
- `AuthError` (unauthorized)
- `GuardError` (guard false)
- `ConstraintError` (constraint false)
- `ConflictError` (idempotency mismatch / concurrency)
- `AdapterError` (backend failure)

Errors MUST be deterministic given identical inputs and history.

---

## 9. Minimal Module Boundaries

Recommended module split:

- `core/ir` (types + validation)
- `core/vm` (Expr evaluator)
- `core/reducer` (ReducerOp executor)
- `runtime/command` (orchestration)
- `runtime/migrate` (replay verification)
- `runtime/http` (transport)
