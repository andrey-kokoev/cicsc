# CICSC Completion TODO (Comprehensive)

## A. Runtime Correctness & Robustness
- [x] Add true transactional API to SQLite/D1 adapter (tx(fn) everywhere)
- [x] Enforce serializable seq allocation under concurrency (SELECT MAX(seq) + INSERT within tx)
- [x] Add snapshot constraint enforcement inside tx for all affected entities (not only touched one)
- [x] Add SLA constraint enforcement inside tx
- [x] Add rollback-safe error propagation for all write paths
- [x] Add idempotency guarantees for duplicate command submissions across restarts
- [x] Add command deduplication windowing (optional: TTL for receipts)

## B. IR Soundness & Type Safety
- [x] Wire IR typechecker into validateBundleV0 and worker load path
- [x] Reject bundles referencing non-materialized row fields (enforced)
- [x] Enforce shadow column type consistency across types
- [x] Enforce reducer writes only to declared attrs/shadows
- [x] Enforce SQL-lowerable intrinsics in views/constraints
- [x] Add static detection of non-deterministic intrinsics in reducers/guards

## C. Schema Generation & Storage Model
- [x] Generate snapshots schema per IR version (vN) from shadows
- [x] Generate indexes from views (order_by, filter fields)
- [x] Generate indexes from constraints (fields referenced in filters)
- [x] Add schema diff/migration generator for snapshots when IR changes
- [x] Add automatic schema install on version activation
- [x] Add per-version event tables (events_vN) management
- [x] Add schema version compatibility checks

## D. SQL Lowering Coverage & Conformance
- [x] Extend SQL lowering to full Query AST coverage (group_by, aggs, joins)
- [x] Extend SQL lowering to full Expr coverage (coalesce, if, in, map_enum, etc.)
- [x] Add differential tests for every Query/Expr operator (SQL vs oracle)
- [x] Add Postgres adapter SQL lowering + exec-vs-oracle conformance tests
- [x] Add performance regression tests for large snapshot tables
- [x] Add explain-plan checks for generated SQL (no full table scans on indexed paths)

## E. Bundle Registry & Multi-Tenancy
- [x] Add bundle registry (R2 or KV): bundle_hash → CoreIrBundleV0
- [x] Add tenant binding table: tenant_id → bundle_hash, active_version
- [x] Modify worker to load bundle by tenant binding (remove CICSC_BUNDLE env)
- [x] Add POST /bundle (store compiled bundle, return bundle_hash)
- [x] Add POST /bind (bind tenant to bundle_hash + version)
- [x] Add GET /bundle/:hash (retrieve bundle)
- [x] Add authz for bundle creation vs tenant binding

## F. Spec DSL (User Intent Layer)
- [x] Define Spec DSL syntax (YAML) distinct from IR shape
- [x] Implement sugar for guards (state predicates, role predicates)
- [x] Implement sugar for reducers (set_state, set_attr, set_shadow shorthand)
- [x] Implement sugar for views (lanes, ordering, limits)
- [x] Implement Spec → IR lowering (non-trivial compiler)
- [x] Add Spec-level typechecking + error reporting (before IR typecheck)
- [x] Add Spec examples for Kanban, Ticketing, CRM
- [x] Add Spec linter (detect anti-patterns, unreachable states, dead commands)

## G. Migrations & Constructive Invariance (CIS → CICSC)
- [x] Define migration spec (event transforms + state mapping)
- [x] Implement migration compiler (Spec vN → Spec vN+1)
- [x] Implement history transformer (events_vN → events_vN+1)
- [x] Implement replay verification for migrations
- [x] Implement cutover protocol (dual-write or pause + migrate + resume)
- [x] Enforce migration totality + executability (reject partial migrations)
- [x] Add migration conformance tests (oracle replay before/after)

## H. Verification & Audit
- [x] Add full-tenant verify (not single entity)
- [x] Add version-stamped verification reports
- [x] Add invariant drift detection across versions
- [x] Add cryptographic hash of event history + snapshots (optional)
- [x] Add audit log export (NDJSON / Parquet)

## I. API & Developer Ergonomics
- [x] Add POST /compile (already stubbed) + persist bundles
- [x] Add POST /install-from-spec (compile + install + bind tenant)
- [x] Add GET /views (list available views)
- [x] Add GET /schema (introspect generated schema)
- [x] Add OpenAPI spec for runtime endpoints
- [x] Add CLI for compile/install/verify
- [x] Add local dev harness (sqlite file + worker emulation)

## J. Performance & Scaling
- [x] Add snapshot compaction policy (periodic snapshotting from events)
- [x] Add projection materialization cache
- [x] Add batched command execution
- [x] Add background SLA evaluation worker
- [x] Add load-shedding / rate limits per tenant
- [x] Add memory bounds for oracle verifier (streaming replay)

## K. Security & Policy
- [x] Formalize auth/role intrinsics contract
- [x] Add policy DSL (optional) compiled to intrinsics
- [x] Add per-command authorization mapping in Spec DSL
- [x] Add row-level security for views
- [x] Add audit trail for policy changes

## L. Documentation & Proofs
- [x] Formalize constructive invariance proof sketch for v0
- [x] Add semantics reference for core calculus (Expr, Query, Reducer)
- [x] Add adapter conformance checklist
- [x] Add “how to build a vertical” guide
- [x] Add migration cookbook
- [x] Add threat model

## M. Stress Verticals (Design Validation)
- [x] Implement CRM vertical Spec (leads, stages, owners, SLAs)
- [x] Implement Kanban vertical Spec (lanes, WIP limits, swimlanes)
- [x] Implement Ticketing v1 Spec (priorities, assignees, escalations)
- [x] Identify missing primitives from real verticals
- [x] Feed primitives back into core calculus (if needed)

## N. Validation, Formalization, and Closure

- [x] Add adversarial test suite for transactional semantics (crash mid-tx, duplicate commands, out-of-order events)
- [x] Add concurrency stress tests (conflicting commands on same entity and across entities)
- [x] Add migration fault-injection tests (partial transforms, schema mismatch, replay failure)
- [x] Add fuzzing for Spec DSL within grammar bounds
- [x] Add fuzzing for IR typechecker (invalid field access, illegal intrinsics, malformed reducers)
- [x] Add cross-backend differential tests (SQLite vs Postgres vs oracle)
- [x] Add history corruption detection tests (tampered events, missing seq)
- [x] Add invariant regression suite (known-bad Specs and migrations)

## O. Canonical Reference Verticals

- [x] Stabilize Kanban Spec v1 (lanes, WIP limits, swimlanes, policies)
- [x] Stabilize Ticketing Spec v1 (priorities, SLAs, escalation rules)
- [x] Stabilize CRM Spec v1 (leads, stages, ownership, conversions)
- [x] Provide minimal migration examples (v0 → v1) for each vertical
- [x] Provide invariant proofs / explanations for each vertical
- [x] Publish performance envelopes for each vertical (ops/sec, latency under load)
- [x] Provide canonical demo datasets for replay verification

## P. Formal Semantics and Specification

- [x] Write formal semantics of event algebra and reducer fold
- [x] Write formal semantics of constraint evaluation (snapshot + bool_query)
- [x] Write formal definition of backend conformance (oracle equivalence)
- [x] Write formal definition of migration correctness (commuting diagrams)
- [x] Specify the Core IR grammar and typing rules
- [x] Specify Spec DSL grammar and desugaring rules
- [x] Define versioning and compatibility rules
- [x] Publish spec as normative reference document

## Q. Kernel Extraction and Hardening

- [ ] Extract kernel package (IR, typechecker, oracle interpreter, migration verifier)
- [ ] Remove HTTP/Workers/SQL dependencies from kernel
- [ ] Add pure in-memory backend for kernel testing
- [ ] Add kernel API stability guarantees
- [ ] Add kernel-level conformance test suite
- [ ] Add minimal embedding examples (CLI, library integration)
- [ ] Document kernel extension points

## R. Release, Stability, and Governance

- [ ] Cut v1.0.0 release tag
- [ ] Define semantic versioning policy for Spec, IR, runtime, kernel
- [ ] Define deprecation policy for Spec constructs
- [ ] Freeze Core IR v1 grammar
- [ ] Add long-term support (LTS) branch
- [ ] Define contribution and review process for semantic changes
- [ ] Define security and vulnerability handling process
- [ ] Archive research branch

## S. Knowledge Externalization

- [ ] Write technical whitepaper / preprint describing CICSC
- [ ] Prepare design note series (core calculus, migrations, conformance)
- [ ] Prepare reference implementation walkthroughs
- [ ] Publish annotated examples for canonical verticals
- [ ] Provide teaching material for Spec DSL
- [ ] Curate “anti-patterns” and failure modes catalog
- [ ] Define glossary of terms and primitives
