# /docs/adapters/postgres.md

# Postgres Adapter — Implementation Guide (Informative)

## 0. Status

This document describes an implementation approach for a CICSC Postgres adapter.

This document is informative. The normative interface is defined in `/docs/spec/adapter-interface.md`.
The declared supported subset contract is tracked in `/tests/conformance/postgres-supported-scope.json`
and mirrored against `/tests/conformance/sqlite-supported-scope.json`.
Constraint conformance matrix is tracked in `/tests/conformance/postgres-constraint-matrix.json`;
reducer conformance is deferred until reducer SQL lowering exists.
NULL/ordering/collation deltas are governed by `docs/spec/backend-semantics-policy.md`.

---

## 1. Capabilities Target

Expected capabilities:

```yaml
capabilities:
  transactions:
    atomic_batch_append: true
    snapshot_in_same_tx: true
  query:
    joins: true
    secondary_indexes: full
    json_extract: true
  constraints:
    snapshot_vm: true
    bool_query: true
  projections:
    query_time: true
    materialized: true
  scheduler:
    cron: false   # use external scheduler by default
```

---

## 2. Storage Layout

### 2.1 Events

Use per-version tables:

```sql
CREATE TABLE events_vX (
  tenant_id   TEXT NOT NULL,
  entity_type TEXT NOT NULL,
  entity_id   TEXT NOT NULL,
  seq         BIGINT NOT NULL,
  event_type  TEXT NOT NULL,
  payload     JSONB NOT NULL,
  ts          BIGINT NOT NULL,
  actor_id    TEXT NOT NULL,
  PRIMARY KEY (tenant_id, entity_type, entity_id, seq)
);
```

Indexes:

```sql
CREATE INDEX ON events_vX (tenant_id, entity_type, entity_id, ts);
CREATE INDEX ON events_vX (tenant_id, entity_type, event_type, ts);
```

Seq allocation:
- Use `SELECT COALESCE(MAX(seq),0)+1 ... FOR UPDATE` within stream
- Or maintain a per-stream counter table with `UPDATE ... RETURNING`

---

### 2.2 Snapshots

```sql
CREATE TABLE snapshots_vX (
  tenant_id   TEXT NOT NULL,
  entity_type TEXT NOT NULL,
  entity_id   TEXT NOT NULL,
  state       TEXT NOT NULL,
  attrs       JSONB NOT NULL,
  updated_ts  BIGINT NOT NULL,
  PRIMARY KEY (tenant_id, entity_type, entity_id)
);
```

Materialized shadows:
- Prefer real columns for heavily queried/order-by fields:

```sql
ALTER TABLE snapshots_vX ADD COLUMN title_txt TEXT;
CREATE INDEX ON snapshots_vX (tenant_id, entity_type, title_txt);
```

If using JSONB for shadows instead:
- Use generated columns or expression indexes, but keep it deterministic.

---

## 3. Constraint Lowering

### 3.1 Snapshot constraints
- Execute in Core VM.

### 3.2 BoolQuery constraints
- Compile Query AST to SQL with parameter binding.
- Prefer `EXISTS` for limit/boolean patterns.
- Prefer `COUNT(*)` for aggregated constraints.

Postgres supports JSONB extraction; adapter MAY avoid shadow columns if:
- it can build stable expression indexes
- deterministic lowering remains stable

---

## 4. View Lowering

Query-time:
- Compile Query AST to SQL, return rows as JSON.

Materialized:
- Optional for high-cost joins/aggregates.

Sorting:
- Prefer SQL ORDER BY.
- Only post-sort if ORDER BY cannot be represented.

---

## 5. SLA Support

If cron is not available inside target:
- expose `sla_check_due` in adapter
- require an external scheduler (e.g., pg_cron, worker process, cloud scheduler)

Use a shared `sla_status` table:

```sql
CREATE TABLE sla_status (
  tenant_id   TEXT NOT NULL,
  name        TEXT NOT NULL,
  entity_type TEXT NOT NULL,
  entity_id   TEXT NOT NULL,
  start_ts    BIGINT,
  stop_ts     BIGINT,
  deadline_ts BIGINT,
  breached    BOOLEAN NOT NULL,
  updated_ts  BIGINT NOT NULL,
  PRIMARY KEY (tenant_id, name, entity_type, entity_id)
);

CREATE INDEX ON sla_status (tenant_id, name, breached, deadline_ts);
```

---

## 6. Migrations

Follow CICSC migration protocol:

- create `events_vX+1`, `snapshots_vX+1`, projections, SLA tables
- transform events by total map function
- replay reducers to rebuild snapshots
- verify constraints/SLAs
- cutover via version pointer

No in-place updates to historical versions.

---

## 7. Determinism Requirements

The adapter MUST ensure:

- stable SQL generation (canonical ordering of predicates, joins, projections)
- stable parameter ordering
- stable serialization formats

---

## 8. Testing Checklist

- append/read stream ordering
- idempotency correctness
- constraint equivalence (VM vs SQL)
- view result determinism
- migration replay verification
- cross-version isolation
