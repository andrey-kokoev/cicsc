# /docs/compiler/sqlite-adapter.md

# SQLite / D1 Adapter — Reference Lowering (Normative)

## 0. Status

This document defines the reference SQLite/D1 adapter for CICSC v0.

This adapter serves as the normative reference implementation of the Target Adapter Interface.

---

## 1. Scope

This adapter targets:

- SQLite 3.x
- Cloudflare D1

The adapter MUST conform to:

- `/docs/spec/adapter-interface.md`
- `/docs/compiler/ir-to-target.md`

---

## 2. Capabilities Declaration

```yaml
capabilities:
  transactions:
    atomic_batch_append: true
    snapshot_in_same_tx: true

  query:
    joins: true
    secondary_indexes: limited
    json_extract: limited

  constraints:
    snapshot_vm: true
    bool_query: true

  projections:
    query_time: true
    materialized: true

  scheduler:
    cron: true
```

---

## 3. Storage Layout

### 3.1 Event Log

```sql
CREATE TABLE events_vX (
  tenant_id   TEXT NOT NULL,
  entity_type TEXT NOT NULL,
  entity_id   TEXT NOT NULL,
  seq         INTEGER NOT NULL,
  event_type  TEXT NOT NULL,
  payload_json TEXT NOT NULL,
  ts          INTEGER NOT NULL,
  PRIMARY KEY (tenant_id, entity_type, entity_id, seq)
);
```

---

### 3.2 Snapshots

```sql
CREATE TABLE snapshots_vX (
  tenant_id   TEXT NOT NULL,
  entity_type TEXT NOT NULL,
  entity_id   TEXT NOT NULL,
  state       TEXT NOT NULL,
  attrs_json  TEXT NOT NULL,
  updated_ts  INTEGER NOT NULL,
  PRIMARY KEY (tenant_id, entity_type, entity_id)
);
```

Shadow columns MUST be added per Core IR:

```sql
ALTER TABLE snapshots_vX ADD COLUMN <shadow_name> <type>;
CREATE INDEX idx_<shadow_name> ON snapshots_vX(tenant_id, entity_type, <shadow_name>);
```

---

## 4. Reducer Lowering

Reducers MUST be lowered to:

- atomic updates of `snapshots_vX`
- atomic insertion into `events_vX`

Reducers MUST execute within a single transaction.

---

## 5. Constraint Lowering

### 5.1 Snapshot Constraints

Snapshot constraints MUST be evaluated by executing Expr AST in the Core VM against the in-memory snapshot.

### 5.2 BoolQuery Constraints

BoolQuery constraints MUST be lowered to SQL EXISTS / COUNT queries.

Compilation MUST fail if a constraint cannot be expressed faithfully.

---

## 6. View Lowering

Views MUST be lowered to:

- SQL SELECT queries over `snapshots_vX`, or  
- materialized projection tables maintained by event projectors.

Sorting and filtering SHOULD be done in SQL where possible.

---

## 7. SLA Lowering

SLAs MUST be lowered to:

- `sla_status` table  
- triggers on event application  
- cron-based deadline checks  

Deadline checks MUST emit events or enforcement actions as defined in Core IR.

---

## 8. Migration Lowering

Migrations MUST be lowered to:

- creation of new `events_vX+1`, `snapshots_vX+1` tables  
- total history transform  
- snapshot and projection rebuild  
- replay verification  

In-place mutation of historical tables is forbidden.

---

## 9. Determinism

Given identical Core IR and preferences, generated schemas and SQL MUST be identical.

---

## 10. Conformance

This adapter is normative.

Any alternative SQLite adapter MUST behave identically to conform to CICSC v0.
