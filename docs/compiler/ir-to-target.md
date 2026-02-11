# Core IR → Target Adapter Lowering (Normative)

## 0. Status

This document defines the normative lowering contract from Core IR v0 to any Target Adapter.

All CICSC adapters MUST implement lowering according to this specification.
Any deviation invalidates CICSC conformance.

---

## 1. Inputs

Lowering consumes:

- Core IR v0 (typed, SQL-free)
- Adapter capability declaration
- Optional compiler preferences

Lowering MUST be deterministic given identical inputs.

---

## 2. Capability Matching

For each Core IR construct, the compiler MUST verify adapter support:

- snapshot constraints → `constraints.snapshot_vm`
- bool_query constraints → `constraints.bool_query`
- joins in queries → `query.joins`
- secondary-index usage → `query.secondary_indexes`
- cron-based SLAs → `scheduler.cron`

If required capabilities are missing, compilation MUST fail.

---

## 3. Physical Representation Selection

### 3.1 Base Tables

Adapters MUST create:

- versioned event log storage
- versioned snapshot storage
- versioned projection storage (if materialized)
- SLA status storage

---

### 3.2 Materialization Rules

Fields referenced in:

- bool_query filters  
- group_by keys  
- order_by keys  
- join keys  

MUST be either:

- natively indexable, or  
- materialized as shadows.

If neither is possible, compilation MUST fail.

---

## 4. Constraint Lowering

### 4.1 Snapshot Constraints

Snapshot constraints MUST be evaluated by executing Expr AST against the in-memory snapshot.

### 4.2 BoolQuery Constraints

BoolQuery constraints MUST be lowered to backend-native queries.

Lowering MUST preserve:

- filter semantics  
- aggregate semantics  
- limit semantics  

Adapters MUST reject queries they cannot faithfully represent.

---

## 5. View Lowering

Views MUST be lowered using either:

- query-time evaluation, or  
- materialized projections.

The choice MUST be deterministic and capability-driven.

If joins are unsupported, views requiring joins MUST be materialized or rejected.

---

## 6. Reducer Lowering

Reducers MUST be lowered to:

- snapshot updates  
- shadow updates  

Reducers MUST execute atomically with event append.

Reducers MUST be deterministic.

---

## 7. SLA Lowering

SLAs MUST be lowered to:

- event-triggered status updates  
- deadline evaluation  
- enforcement actions  

If the adapter does not support internal scheduling, SLA checking MUST be exposed for external scheduling.

---

## 8. Migration Lowering

Migrations MUST be lowered to:

- creation of new versioned storage  
- total history transform  
- snapshot and projection rebuilds  
- replay verification

Adapters MUST NOT perform in-place mutation of historical data.

---

## 9. Determinism and Reproducibility

Lowering MUST be deterministic.

Generated schemas, queries, and runtime code MUST be identical for identical inputs.

---

## 10. Failure Modes

Lowering MUST fail if:

- any Core IR construct cannot be represented  
- any required materialization cannot be performed  
- any semantic guarantee cannot be preserved  
- any migration is partial or unverifiable  

Compilation failure is the only valid response to unsupported semantics.
