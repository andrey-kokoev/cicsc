# /docs/spec/adapter-interface.md

# Target Adapter Interface (Normative)

## 0. Status

This document defines the normative Target Adapter Interface for CICSC v0.

Any backend integration MUST implement this interface.
Any deviation invalidates CICSC conformance.

---

## 1. Purpose

The Target Adapter is responsible for lowering Core IR semantics into concrete runtime behavior on a specific backend.

The adapter is the only layer permitted to reference:

- storage technology
- query dialects
- scheduling mechanisms
- transactional semantics

Core IR and Spec DSL MUST remain backend-agnostic.

---

## 2. Adapter Capabilities Declaration

Adapters MUST declare capabilities:

```yaml
capabilities:
  transactions:
    atomic_batch_append: true|false
    snapshot_in_same_tx: true|false

  query:
    joins: true|false
    secondary_indexes: none|limited|full
    json_extract: true|false

  constraints:
    snapshot_vm: true|false
    bool_query: true|false

  projections:
    query_time: true|false
    materialized: true|false

  scheduler:
    cron: true|false
```

Compilation MUST fail if Core IR requires unsupported capabilities.

---

## 3. Storage Interface

### 3.1 Event Log

Adapters MUST implement:

- `append_events(tenant, entity_type, entity_id, events[], idempotency_key)`
- `read_stream(tenant, entity_type, entity_id, from_cursor?)`
- `query_events(tenant, query_spec?)` (optional; required for SLA rebuilds)

Properties:

- append MUST be atomic per batch  
- events MUST be immutable once committed  
- event order MUST be deterministic  

---

### 3.2 Snapshots

Adapters MUST implement:

- `get_snapshot(tenant, entity_type, entity_id)`
- `put_snapshot(tenant, entity_type, entity_id, snapshot, version_marker)`
- `query_snapshots(tenant, entity_type, filter_spec, order_spec, limit, cursor?)`

Properties:

- snapshots MUST be reducible from event history  
- snapshot updates MUST be atomic with event append  

---

## 4. Constraint Evaluation

Adapters MUST implement:

- `eval_constraint(tenant, constraint_id, args, ctx) -> bool`

Rules:

- snapshot constraints MAY be delegated to the Core VM  
- bool_query constraints MUST be lowered to backend-native queries  
- constraints MUST be evaluated within the same transaction as command execution  

---

## 5. Projections

Adapters MUST support:

- `exec_view_query(tenant, view_id, params)`
- `apply_projection_event(tenant, view_id, event)` (if materialized projections are used)
- `rebuild_projection(tenant, view_id, from_events_query)` (for migrations)

Rules:

- view results MUST reflect Core IR semantics  
- adapters MAY choose query-time or materialized strategies per view  

---

## 6. SLA Support

Adapters MUST implement:

- `sla_apply_event(tenant, sla_id, entity_type, entity_id, event)`
- `sla_check_due(tenant, now, sla_id, limit)`
- `sla_mark_breached(tenant, sla_id, breach)`

If `capabilities.scheduler.cron = false`, adapters MUST expose `sla_check_due` for external scheduling.

---

## 7. Versioning and Migrations

Adapters MUST implement:

- `get_active_version(tenant)`
- `set_active_version(tenant, version)`
- `create_versioned_storage(tenant, version)`
- `materialize_migration(tenant, from_version, to_version, transform_event_fn, rebuild_plan)`

Rules:

- migrations MUST be total over history  
- migrations MUST be replay-verified  
- adapters MUST NOT mutate historical tables in-place  

---

## 8. Error Handling

Adapters MUST fail compilation or execution if:

- Core IR requires unsupported capabilities  
- a constraint cannot be lowered faithfully  
- migrations are partial or non-total  
- replay verification fails  

Partial implementations are non-conforming.

---

## 9. Conformance

An adapter conforms to CICSC v0 iff:

- it implements all mandatory interface methods  
- it declares capabilities truthfully  
- it rejects unsupported Core IR features  
- it preserves Core IR semantics exactly  

Non-conforming adapters MUST NOT claim CICSC compatibility.
```
