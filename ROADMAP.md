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

- [x] Extract kernel package (IR, typechecker, oracle interpreter, migration verifier)
- [x] Remove HTTP/Workers/SQL dependencies from kernel
- [x] Add pure in-memory backend for kernel testing
- [x] Add kernel API stability guarantees
- [x] Add kernel-level conformance test suite
- [x] Add minimal embedding examples (CLI, library integration)
- [x] Document kernel extension points

## R. Release, Stability, and Governance

- [x] Cut v1.0.0 release tag
- [x] Define semantic versioning policy for Spec, IR, runtime, kernel
- [x] Define deprecation policy for Spec constructs
- [x] Freeze Core IR v1 grammar
- [x] Add long-term support (LTS) branch
- [x] Define contribution and review process for semantic changes
- [x] Define security and vulnerability handling process
- [x] Archive research branch

## S. Knowledge Externalization

- [x] Write technical whitepaper / preprint describing CICSC
- [x] Prepare design note series (core calculus, migrations, conformance)
- [x] Prepare reference implementation walkthroughs
- [x] Publish annotated examples for canonical verticals
- [x] Provide teaching material for Spec DSL
- [x] Curate “anti-patterns” and failure modes catalog
- [x] Define glossary of terms and primitives

## T. Phase 3 Forced Follow-Ups

- [x] Resolve oracle replay + constraints regression currently failing `tests/oracle/replay-and-constraints.test.ts`
- [x] Standardize local/CI dependency bootstrap for adapter checks (`pg`, sqlite test harness drivers)
- [x] Promote the Phase 3 CI target (`scripts/phase3_ci_target.sh`) to default validation entrypoint in automation
- [x] Add deterministic policy for `.ts` module resolution in test runtime (remove ad hoc execution variance)

## U. Phase 5: Deployment-Grade Semantic Closure

### U1. Conformance Gate Enforcement

- [x] U1.1 Define required conformance suite matrix (sqlite + postgres where supported)
- [x] U1.2 Promote sqlite execution-vs-oracle matrix to required CI gate
- [x] U1.3 Add differential coverage for join/group/having/subquery operators in supported scope (having deferred until Query AST support)
- [x] U1.4 Gate merges on conformance coverage threshold and no untracked regressions
- [x] U1.5 Add deterministic replay artifact retention policy for CI failures

### U2. Migration Cutover and Rollback Protocol

- [x] U2.1 Define executable migration preflight checklist (`SafeMigration` + runtime preconditions)
- [x] U2.2 Implement migration dry-run with replay verification report artifact
- [x] U2.3 Implement cutover workflow with explicit pause/switch/resume boundaries
- [x] U2.4 Implement rollback workflow for reversible subset with explicit failure handling
- [x] U2.5 Add operator runbook and CLI commands for preflight/cutover/rollback

### U3. Spec DSL Ergonomics and Compiler Guarantees

- [x] U3.1 Freeze v1 Spec DSL grammar and desugaring contract
- [x] U3.2 Add compiler diagnostics with path-qualified errors for all rejected constructs
- [x] U3.3 Add negative compiler tests for invariant-weakening patterns
- [x] U3.4 Add roundtrip fixtures (`spec -> ir -> validated semantics artifacts`)
- [x] U3.5 Add documentation and examples for non-programmer-authored workflows

### U4. Bundle Registry and Tenant Binding

- [x] U4.1 Implement bundle registry API/storage contract (publish, resolve, pin)
- [x] U4.2 Implement tenant-to-bundle/version binding with immutable audit trail
- [x] U4.3 Implement bundle signature/hash verification on install
- [x] U4.4 Add lifecycle tests for publish/bind/upgrade/rollback
- [x] U4.5 Add policy controls for who may bind or migrate tenant bundles

### U5. Postgres Adapter Semantic Parity

- [x] U5.1 Define Postgres supported-scope contract mirroring sqlite scope model
- [x] U5.2 Add postgres execution-vs-oracle differential matrix for in-scope operators
- [x] U5.3 Add postgres constraint/reducer conformance checks where lowering exists
- [x] U5.4 Align NULL/ordering/collation semantics policy and document deltas
- [x] U5.5 Add cross-backend consistency gate (sqlite vs postgres vs oracle)

### U6. Field Validation Vertical

- [x] U6.1 Select one reference vertical and freeze evaluation criteria
- [x] U6.2 Run staged workload with invariants, conformance, and migration checks enabled
- [x] U6.3 Capture drift/perf/missing-primitive incidents with severity labels
- [x] U6.4 Convert findings into roadmap checkboxes (no hidden backlog)
- [x] U6.5 Publish phase report with forced-next priorities only

### U7. Governance Gate for Phase 6

- [x] U7.1 Define objective Phase 5 exit checklist mapped to artifacts
- [x] U7.2 Require green required conformance gates for sqlite + postgres scoped matrices
- [x] U7.3 Require migration runbook and cutover/rollback drill evidence
- [x] U7.4 Require Spec DSL usability evidence from reference vertical
- [x] U7.5 Add CI/doc checks rejecting unchecked claims in phase/status docs

## V. Field-Derived Backlog (Ticketing Phase 5)

- [x] V1 Resolve `INC-PG-HARNESS-001`: add/install postgres test harness dependency (`pg-mem`) and make postgres gate executable in default developer bootstrap.
- [x] V2 Resolve `INC-ORDER-COLLATION-001`: add explicit NULL ordering/collation controls in lowering/typecheck policy (remove backend-default ambiguity).
- [x] V3 Resolve `INC-PERF-BASELINE-001`: add staged-run latency/throughput instrumentation and artifact SLO thresholds.

## W. Phase 6: Field-Driven Concurrency Expansion

### W1. Multi-Vertical Field Expansion

- [x] W1.1 Select second reference vertical and freeze evaluation criteria artifact
- [x] W1.2 Run staged workload for second vertical with invariant/conformance/migration gates
- [x] W1.3 Add comparative incident register (ticketing vs second vertical) with severity/recurrence tags
- [x] W1.4 Convert comparative findings into explicit roadmap checkboxes (no hidden backlog)
- [x] W1.5 Publish Phase 6 field baseline report with forced-next priorities only

Comparative incident mapping:
- `CINC-CONFORMANCE-001` -> `W4.2`
- `CINC-SPEC-USABILITY-001` -> `W3.5`
- `CINC-MIGRATION-001` -> `W2.4`

### W2. Concurrency Contract Hardening

- [x] W2.1 Define explicit supported concurrency model contract (stream + cross-stream boundaries)
- [x] W2.2 Add causality/partial-order replay conformance suite for declared model
- [x] W2.3 Add deterministic conflict outcome matrix (abort/retry/merge) with proofs/tests per case
- [x] W2.4 Add migration-under-concurrency drill under concurrent load
- [x] W2.5 Publish updated isolation/concurrency normative note with scoped exclusions

### W3. Proven-Surface Productization

- [x] W3.1 Freeze CLI command contract for compile/install/migrate/verify/gates
- [x] W3.2 Add SDK contract tests for bundle lifecycle and tenant binding policies
- [x] W3.3 Add operator playbook for multi-tenant rollout/rollback/incident triage
- [x] W3.4 Add policy control matrix with executable checks
- [x] W3.5 Add proven-vs-experimental feature gating across docs/API surfaces

### W4. Governance Gate for Phase 7

- [x] W4.1 Define objective Phase 6 exit checklist mapped to artifacts
- [x] W4.2 Require green dual-backend conformance + concurrency suites
- [x] W4.3 Require multi-vertical field report with unresolved criticals closed or explicitly deferred
- [x] W4.4 Add CI/doc checks rejecting phase/status drift for Phase 6 artifacts
- [x] W4.5 Block Phase 7 unless all checklist items are pass

## X. Phase 7: Semantic Equivalence Hardening

### X1. Cross-Backend Semantic Parity

- [x] X1.1 Freeze Phase 7 parity scope matrix (operators/null/collation/numeric behavior)
- [x] X1.2 Add full in-scope sqlite/postgres/oracle differential suites
- [x] X1.3 Enforce fail-fast rejection for out-of-scope operators
- [x] X1.4 Publish backend parity report with explicit exclusions
- [x] X1.5 Convert unresolved parity deltas into explicit roadmap items

Phase 7 parity delta mapping:
- `PDELTA-HAVING-001` -> `X1.3`
- `PDELTA-SETOP-001` -> `X1.3`
- `PDELTA-COLLATION-001` -> `X2.5`
- `PDELTA-NUMERIC-001` -> `X2.3`

### X2. Concurrency and Isolation Strengthening

- [x] X2.1 Define Phase 7 concurrency contract delta over Phase 6 baseline
- [x] X2.2 Add adversarial multi-tenant + cross-stream replay suites
- [x] X2.3 Add backend isolation differential checks for declared invariants
- [x] X2.4 Expand deterministic conflict outcome matrix coverage
- [x] X2.5 Publish updated isolation note with strengthened guarantees + exclusions

### X3. Migration and Operational Contract Hardening

- [x] X3.1 Freeze executable migration protocol contract
- [x] X3.2 Add tenant-batch fault-injected migration drills with deterministic recovery checks
- [x] X3.3 Add post-cutover SQL execution-vs-oracle differential checks
- [x] X3.4 Add migration/verify SLO and error-budget artifact
- [x] X3.5 Publish migration safety report with critical disposition closure

### X4. Governance Gate for Phase 8

- [x] X4.1 Define objective Phase 7 exit checklist mapped to artifacts
- [x] X4.2 Require green required gates (parity + concurrency + migration protocol)
- [x] X4.3 Require unresolved criticals register empty or explicitly deferred with owner/date
- [x] X4.4 Add CI/doc checks rejecting Phase 7 status drift
- [x] X4.5 Block Phase 8 unless all checklist items are pass

## Y. Phase 8: Production Equivalence and Scale Hardening

### Y1. Production-Equivalence Backend Hardening

- [x] Y1.1 Freeze production-equivalence scope matrix (workload envelope + data diversity)
- [x] Y1.2 Add large-snapshot/high-cardinality sqlite/postgres/oracle differential suites
- [x] Y1.3 Add deterministic parity checks for null/collation/numeric edge-case datasets
- [x] Y1.4 Publish production-equivalence report with exclusions and risk labels
- [x] Y1.5 Convert unresolved production-equivalence risks into explicit roadmap items

Phase 8 production-equivalence risk mapping:
- `PRISK-COLLATION-001` -> `Y1.3`
- `PRISK-NUMERIC-001` -> `Y1.3`
- `PEXCL-HAVING-001` -> `Y1.5`
- `PEXCL-EXISTS-001` -> `Y1.5`

### Y2. Multi-Tenant Operational Resilience

- [x] Y2.1 Define Phase 8 operational resilience contract
- [x] Y2.2 Add multi-tenant chaos drills (outage/verify delay/replay backpressure)
- [x] Y2.3 Add tenant fairness and starvation checks for command execution
- [x] Y2.4 Add continuous SLO/error-budget gate for verify/migrate/command paths
- [x] Y2.5 Publish resilience report with failed scenarios closed or explicitly deferred

### Y3. Spec and Migration Ergonomics at Scale

- [x] Y3.1 Freeze spec authoring pain-point taxonomy from field evidence
- [x] Y3.2 Add DSL ergonomics improvements with negative typecheck coverage
- [x] Y3.3 Add migration authoring assistant checks (coverage/safety/rollback readiness)
- [x] Y3.4 Add multi-vertical spec/migration usability benchmark artifact
- [x] Y3.5 Publish ergonomics report with invariant-safety confirmation

### Y4. Governance Gate for Phase 9

- [x] Y4.1 Define objective Phase 8 exit checklist mapped to artifacts
- [x] Y4.2 Require green required gates (equivalence + resilience + ergonomics safety)
- [x] Y4.3 Require unresolved criticals register empty or explicitly deferred with owner/date
- [x] Y4.4 Add CI/doc checks rejecting Phase 8 status drift
- [x] Y4.5 Block Phase 9 unless all checklist items are pass

## Z. Phase 9: Capability Expansion Under Guarded Equivalence

### Z1. SQL Capability Expansion With Conformance

- [x] Z1.1 Freeze Phase 9 SQL scope matrix (supported/deferred operators and query forms)
- [x] Z1.2 Implement selected deferred query lowering candidates (`HAVING`, `EXISTS`) behind explicit gates
- [x] Z1.3 Add SQL execution-vs-oracle differential suites for each newly enabled construct
- [x] Z1.4 Add negative typecheck coverage for unsupported forms to enforce compile-time rejection
- [x] Z1.5 Publish SQL-surface closure report with residual exclusions and risk labels

### Z2. Cross-Backend Parity Hardening (SQLite + Postgres)

- [x] Z2.1 Freeze backend parity contract for Phase 9 (semantic classes + scale envelope)
- [x] Z2.2 Add deterministic cross-backend edge-case suites (null/collation/numeric/time behavior)
- [x] Z2.3 Add seeded random differential sweeps for SQLite/Postgres/oracle over expanded operators
- [x] Z2.4 Add parity triage artifact with regression class labeling and owner assignment
- [x] Z2.5 Publish backend parity report and required-gates policy update

### Z3. Migration + Operational Reliability on Expanded Surface

- [x] Z3.1 Extend migration protocol contract for newly supported SQL/query constructs
- [x] Z3.2 Add migration drill suites covering upgraded features (preflight/dry-run/cutover/rollback)
- [x] Z3.3 Add post-cutover execution-vs-oracle differential checks on migrated streams
- [x] Z3.4 Add updated SLO/error-budget gates for verify/migrate/command paths under expanded load
- [x] Z3.5 Publish migration safety and operations report with unresolved criticals disposition

### Z4. Deployment Validation and Governance Gate for Phase 10

- [x] Z4.1 Select and freeze Phase 9 reference deployment set (at least two verticals)
- [x] Z4.2 Run scripted workloads with invariants + parity + migration gates enabled
- [x] Z4.3 Capture drift/missing-primitive/performance findings with severity labels
- [x] Z4.4 Convert findings into forced-next roadmap tasks (no speculative backlog inflation)
- [x] Z4.5 Define and enforce objective Phase 9 exit checklist + Phase 10 block gate

Phase 9 forced-next mapping:
- `P9FIND-PARITY-HAVING-PG-001` -> `P10-PARITY-HAVING-HARNESS`
- `P9FIND-SQL-EXISTS-001` -> `P10-SQL-EXISTS-LOWERING`
- `P9FIND-OPS-GATE-001` -> `P10-OPS-GATE-CONTINUITY`

## AA. Phase 10: Forced-Next Closure and Production Parity Continuity

### AA1. Forced-Next SQL and Parity Closure

- [x] AA1.1 Freeze forced-next execution scope and ownership contract
- [x] AA1.2 Add Postgres HAVING harness continuity artifact and validation test
- [x] AA1.3 Publish EXISTS lowering decision contract (enablement or explicit deferred policy)
- [x] AA1.4 Add forced-next execution status register with owner/date discipline

### AA2. Production Parity Continuity Gates

- [x] AA2.1 Add unified Phase 10 parity continuity gate script/report
- [x] AA2.2 Add unified Phase 10 migration continuity gate script/report
- [x] AA2.3 Add unified Phase 10 operational SLO continuity gate script/report
- [x] AA2.4 Publish Phase 10 continuity report with unresolved criticals policy

### AA3. Governance Gate for Phase 11

- [x] AA3.1 Define objective Phase 10 exit checklist mapped to artifacts
- [x] AA3.2 Add PHASE10↔ROADMAP status-drift consistency gate
- [x] AA3.3 Add Phase 11 block gate based on Phase 10 checklist
- [x] AA3.4 Publish Phase 10 closure report and mark exit criteria

## AB. Phase 11: Envelope Expansion Under Equivalence Discipline

### AB1. Scope Freeze and Governance Baseline

- [x] AB1.1 Freeze Phase 11 scope and objective ownership contract
- [x] AB1.2 Publish Phase 11 baseline gate snapshot (parity/migration/ops/governance)
- [x] AB1.3 Add Phase 11 status register with owner/date accountability

### AB2. DSL Usability Closure

- [x] AB2.1 Define non-programmer task suite and success rubric
- [x] AB2.2 Add reproducible usability harness and evidence artifact
- [x] AB2.3 Publish DSL usability closure report with residuals policy

### AB3. SQL/Parity Deferred Closure

- [x] AB3.1 Freeze deferred SQL/parity item ledger and closure plan
- [x] AB3.2 Add differential harnesses for selected deferred constructs
- [x] AB3.3 Publish deferred-item disposition report (closed vs deferred with owner/date)

### AB4. Deployment Expansion and Phase 12 Gate

- [x] AB4.1 Freeze expanded deployment set and workload contract
- [x] AB4.2 Run expanded workload suite with parity/migration/ops gates
- [x] AB4.3 Capture drift/performance/missing-primitive findings with severity labels
- [x] AB4.4 Add objective Phase 11 exit checklist and Phase 12 block gate

## AC. Phase 12: Broad Deployment Generalization Under Kernel Discipline

### AC1. Scope Freeze and Baseline Continuity

- [x] AC1.1 Freeze Phase 12 scope and owner contract
- [x] AC1.2 Publish Phase 12 baseline continuity snapshot
- [x] AC1.3 Add Phase 12 status register with owner/date discipline

### AC2. Multi-Domain Deployment Expansion

- [x] AC2.1 Freeze expanded domain matrix and workload contract
- [x] AC2.2 Run expanded multi-domain workload suites with required gates
- [x] AC2.3 Publish deployment expansion report with findings disposition

### AC3. Backend Parity Envelope Widening

- [x] AC3.1 Freeze parity envelope extension matrix
- [x] AC3.2 Add differential harnesses for newly included envelope items
- [x] AC3.3 Publish parity envelope closure report with residual policy

### AC4. Governance Closure and Phase 13 Gate

- [ ] AC4.1 Define objective Phase 12 exit checklist mapped to artifacts
- [ ] AC4.2 Add PHASE12↔ROADMAP drift consistency gate
- [ ] AC4.3 Add Phase 13 block gate from Phase 12 checklist
- [ ] AC4.4 Publish Phase 12 closure report and mark exit criteria
