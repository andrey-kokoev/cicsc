# LEAN_KERNEL_V2.md
## CICSC Lean Kernel v2 Milestone: Feature Completeness

**Current State:** v1.5 coherency-complete (9.8/10 alignment with AGENTS.md)
**Target State:** v2 with full query algebra, SQL conformance, and concurrency properties

This document defines feature additions beyond v1.5 coherency completion.
v2 focuses on **expanding the semantic surface** rather than closing proof gaps.

---

## Milestone Definition

v2 adds semantic coverage for:
1. **Full Query Algebra** - joins, groupBy, aggregations beyond the v1 subset
2. **SQL Conformance** - prove TypeScript SQL lowering matches Lean QueryEval
3. **Concurrency Properties** - transactional isolation, event ordering guarantees
4. **Typechecker Completeness** - bidirectional `HasType ↔ inferExprTy` equivalence
5. **Bundle Evolution** - multi-step migration composition and rollback semantics

---

## 0. v2 Scope

### In scope (must be semantically defined and proved)
- Full relational query algebra (joins, groupBy, aggregations)
- SQL backend conformance (QueryEval ≈ SQLite/Postgres execution)
- Transactional isolation levels (read committed, serializable)
- Event ordering and causality properties
- Migration composition and commutativity
- Typechecker bidirectional completeness

### Out of scope (deferred to v3+)
- Distributed system properties (CAP, consensus)
- Performance models and complexity bounds
- Live migration (zero-downtime cutover)
- Full SQL feature parity (window functions, CTEs, etc.)
- Verification condition generation for arbitrary user code

---

## 1. Full Query Algebra

### 1.1 Join Semantics

**Objective:** Define and prove correct semantics for join operations

#### 1.1.1 Join Types
- [x] Define `evalJoin : JoinType → List QueryRow → List QueryRow → Expr → List QueryRow`
  - Implemented in `lean/Cicsc/Core/Semantics/QueryEval.lean` as the canonical join evaluator.
  - Definitional lemmas `evalJoin_cross_def` and `evalJoin_inner_def` fix the executable meaning for core join cases.
  - `JoinType ::= Inner | LeftOuter | RightOuter | FullOuter | Cross`
  - Join condition as Expr (evaluated on combined row environment)
- [x] Implement join evaluation:
  - Cross join: Cartesian product
  - Inner join: Filter on join predicate
  - Outer joins: Include nulls for unmatched rows
- [x] Define row combination semantics:
  - `combineRows : QueryRow → QueryRow → QueryRow` (merge field lists)
  - Prove field name collision handling (prefer left/right based on join type)

#### 1.1.2 Join Properties
- [x] Prove join commutativity (where applicable):
  - Covered by `crossJoin_commutative_modulo_combineRows`.
  - Covered by `innerJoin_symmetric_condition_produces_symmetric_results` under explicit symmetry premise on join condition.
  - `evalJoin Inner a b e = evalJoin Inner b e[swapped] a` (modulo row order)
- [ ] Prove join associativity for inner joins:
  - `(a ⋈ b) ⋈ c = a ⋈ (b ⋈ c)` (modulo projection)
- [x] Prove outer join non-commutativity examples
  - Covered by `outerJoin_noncommutative_concrete` in `lean/Cicsc/Core/Semantics/QueryEval.lean`.
- [x] Define and prove join elimination rules:
  - `(a ⋈ b) WHERE false = ∅` covered by `innerJoin_false_condition_empty`.
  - `cross join + filter` equivalence to inner join covered by `crossJoin_then_filter_eq_innerJoin`.
  - Duplicate-free right-side elimination covered by `innerJoin_dedup_right_equiv`.
  - `(a ⋈ b) WHERE false = ∅`
  - `a ⋈ (SELECT DISTINCT ...) = a ⋈ ...` (under conditions)

#### 1.1.3 Multi-Source Queries
- [x] Extend `Source` to support multiple snap sources
  - `Source.join` supports recursive multi-source trees.
  - `multiSnapSource` in `lean/Cicsc/Core/Semantics/QueryEval.lean` constructs multi-snap join sources.
- [x] Define join ordering and optimization hints (logical plan vs physical plan split)
  - `JoinOrder`, `PhysicalHints`, `LogicalPlan`, and `PhysicalPlan` are defined in `lean/Cicsc/Core/Syntax.lean`.
  - `applyJoinOrder`, `logicalToPhysical`, and `evalPhysicalPlan` are defined in `lean/Cicsc/Core/Semantics/QueryEval.lean`.
- [ ] Prove plan equivalence for different join orders (when semantically identical)

**Acceptance:**
- All join types have formal semantics
- Join properties proved for supported fragment
- Multi-table queries work in Examples

---

### 1.2 GroupBy and Aggregations

**Objective:** Define aggregation semantics over grouped rows

#### 1.2.1 Grouping Semantics
- [x] Define `evalGroupBy : List Expr → List QueryRow → List (List Expr × List QueryRow)`
  - Implemented as typed-key variant `evalGroupBy : List GroupKey → List QueryRow → List (List Val × List QueryRow)` in `lean/Cicsc/Core/Semantics/QueryEval.lean`.
  - Group rows by equivalence classes on grouping expressions
  - Return groups with their key values
- [x] Define aggregation functions:
  - `AggExpr` includes `COUNT`, `SUM`, `AVG`, `MIN`, `MAX`, `STRING_AGG` in `lean/Cicsc/Core/Syntax.lean`.
  - `COUNT`, `SUM`, `AVG`, `MIN`, `MAX`, `STRING_AGG`
- [x] Define `evalAggregate : AggFn → List QueryRow → Val`
  - Implemented as `evalAggregate : AggExpr → List QueryRow → Val` in `lean/Cicsc/Core/Semantics/QueryEval.lean`, with empty-group behavior and aggregate laws captured by local theorems.
  - Handle empty groups (COUNT=0, others=NULL)
  - Prove aggregation commutativity/associativity where applicable

#### 1.2.2 HAVING Clause
- [x] Extend Query with `HAVING Expr` (filter on aggregated results)
  - `QueryOp.having` is defined in `lean/Cicsc/Core/Syntax.lean`.
  - Evaluated in `applyQueryOpSubset` in `lean/Cicsc/Core/Semantics/QueryEval.lean`.
- [x] Define evaluation order: GROUP BY → aggregation → HAVING → projection
  - Canonical ordering is encoded in `evalGroupByQuery`.
  - Definitional theorem `evalGroupByQuery_order` fixes the order explicitly.
- [ ] Prove HAVING vs WHERE distinction (pre-grouping vs post-aggregation)

#### 1.2.3 GroupBy Properties
- [ ] Prove aggregation distributes over UNION (where applicable):
  - `SUM(a UNION ALL b) = SUM(a) + SUM(b)` (for compatible schemas)
- [ ] Prove GROUP BY with single group = global aggregation
- [ ] Define and prove NULL handling in grouping keys

**Acceptance:**
- All SQL standard aggregations have formal semantics
- GROUP BY + HAVING works in Examples
- Properties proved for distributive aggregations

---

### 1.3 Query Algebra Completeness

#### 1.3.1 Set Operations
- [x] Define `evalUnion`, `evalIntersect`, `evalExcept` over QueryRow sets
  - Set operators are implemented in `lean/Cicsc/Core/Semantics/QueryEval.lean` via `applySetOp`.
  - Canonical query evaluation path (`evalQuery`) now executes `.setOp` via `evalQuerySubsetWithSetOps` in `lean/Cicsc/Core/Semantics/QueryEval.lean`.
- [x] Prove set operation properties:
  - Union commutativity, associativity
  - Intersection commutativity, idempotence
  - De Morgan's laws for set operations
- [x] Define DISTINCT semantics and prove relationship to set operations
  - `evalDistinct` defined in `lean/Cicsc/Core/Semantics/QueryEval.lean`.
  - `evalUnionDistinct_eq_distinct_union` links DISTINCT to UNION semantics.
  - `evalDistinct_idempotent` captures DISTINCT idempotence.

#### 1.3.2 Subqueries
- [x] Define correlated subquery semantics (row-dependent evaluation)
  - `evalCorrelatedSubquery` defined in `lean/Cicsc/Core/Semantics/QueryEval.lean`.
  - Outer-row field preservation captured by `correlated_subquery_preserves_outer_fields`.
- [x] Define EXISTS, IN, ANY, ALL predicates over subqueries
  - `existsSubquery`, `inSubquery`, `anySubquery`, and `allSubquery` defined in `lean/Cicsc/Core/Semantics/QueryEval.lean`.
- [x] Prove subquery flattening equivalences (decorrelation rules)
  - Restricted decorrelation laws are proved for current correlated encoding:
    - `exists_correlated_flatten`
    - `any_correlated_flatten`

#### 1.3.3 Relational Algebra Equivalences
- [x] Prove selection pushdown: `σ(a ⋈ b) = σ(a) ⋈ b` (when predicate references only a)
  - Restricted theorem `selection_pushdown_cross_left` proved for cross-join fragment with explicit left-only predicate premise.
- [ ] Prove projection pushdown rules
- [ ] Define query normalization and prove equivalence classes

**Acceptance:**
- Full relational algebra operators defined
- Classical equivalences proved
- Query optimization hints have semantic justification

---

## 2. SQL Conformance

### 2.1 SQL Lowering Specification

**Objective:** Formalize the TypeScript SQL lowering and prove it matches Lean semantics

#### 2.1.1 SQL AST Representation
- [x] Define Lean representation of SQL AST:
  - Added `lean/Cicsc/Sql/Ast.lean` with `SQLExpr`, `SQLFrom`, `SQLJoinType`, `SQLOrderBy`, and `SQLQuery`.
  - `SQLQuery`, `SQLExpr`, `SQLJoin`, `SQLGroupBy`, etc.
- [ ] Define `lowerQuery : Query → SQLQuery` (Lean version of TS lowering)
- [ ] Define `lowerExpr : Expr → SQLExpr`

#### 2.1.2 SQL Execution Model
- [ ] Define abstract SQL execution semantics:
  - `execSQL : SQLQuery → DB → List Row` (DB = snapshot database state)
  - Model SQLite/Postgres evaluation order
- [ ] Define row/value representation mapping:
  - Lean `Val` ↔ SQL types (INTEGER, TEXT, BLOB, NULL)
  - Handle type coercion rules

#### 2.1.3 Conformance Theorem
- [ ] **Main Theorem:** `execSQL (lowerQuery q) db ≈ evalQuery ir q (snapFromDB db)`
  - "≈" = row-set equivalence modulo order (for unordered queries)
  - `snapFromDB` converts SQL DB state to Lean SnapSet
- [ ] Prove for supported subset first, then extend to full algebra
- [ ] Document limitations where SQL and Lean semantics diverge:
  - NULL propagation edge cases
  - String collation differences
  - Floating point precision

**Acceptance:**
- Lowering function defined in Lean
- Conformance theorem proved for v1 subset
- Path to extending proof for v2 features documented

---

### 2.2 Differential Testing Framework

**Objective:** Executable conformance tests between Lean oracle and SQL backends

#### 2.2.1 Test Generator
- [ ] Define property-based test generator:
  - Generate random Query + SnapSet pairs
  - Generate random IR schemas
  - Ensure generated queries are well-typed
- [ ] Define test oracle:
  - Run `evalQuery` in Lean (via `#eval`)
  - Run lowered SQL against SQLite
  - Compare result sets (modulo order)

#### 2.2.2 Conformance Test Suite
- [ ] Add 100+ differential tests covering:
  - All query operators (filter, project, join, groupBy, etc.)
  - Edge cases (empty results, NULLs, type coercion)
  - Nested queries and correlated subqueries
- [ ] Integrate into CI: fail build if Lean oracle ≠ SQL execution

**Acceptance:**
- Differential tests exist and pass
- Any Lean/SQL divergence is documented as known limitation
- Test coverage > 90% of QueryEval code paths

---

## 3. Concurrency Properties

### 3.1 Event Ordering and Causality

**Objective:** Formalize happens-before relationships and prove ordering guarantees

#### 3.1.1 Happens-Before Relation
- [ ] Define `happensBefore : Event → Event → Prop`:
  - Same stream + lower seq → happens-before
  - Cross-stream causality via command emits (if tracked)
- [ ] Prove happens-before is a partial order (transitive, antisymmetric)
- [ ] Define causal histories: `isCausal : History → Prop` (respects seq ordering per stream)

#### 3.1.2 Replay Causality
- [ ] Prove replay respects causality:
  - If `happensBefore e1 e2` and both in stream, then `e1` applied before `e2`
- [ ] Prove replay commutativity for concurrent events:
  - If `¬happensBefore e1 e2 ∧ ¬happensBefore e2 e1`, order doesn't affect final state (for commutative reducers)
- [ ] Define and prove deterministic replay:
  - `replay ir sid h1 = replay ir sid h2` if `h1` and `h2` have same causal structure

**Acceptance:**
- Happens-before relation formalized
- Causality properties proved
- Examples demonstrate concurrent event handling

---

### 3.2 Transactional Isolation

**Objective:** Model isolation levels and prove snapshot isolation guarantees

#### 3.2.1 Snapshot Isolation Model
- [ ] Define snapshot reads:
  - `snapshotAt : History → Timestamp → StreamId → State`
  - Returns state as of timestamp (includes all events with ts ≤ T)
- [ ] Define transaction visibility rules:
  - Read committed: see all committed events before transaction start
  - Snapshot isolation: see consistent snapshot at start timestamp
  - Serializable: as if transactions executed sequentially

#### 3.2.2 Isolation Guarantees
- [ ] Prove snapshot isolation prevents:
  - Dirty reads (never see uncommitted state)
  - Non-repeatable reads (snapshot doesn't change mid-transaction)
  - Phantom reads (for snapshot-based queries)
- [ ] Prove write-write conflict detection:
  - If two transactions modify same stream concurrently, one must abort
- [ ] Model and prove serializability for conflict-free reducers

**Acceptance:**
- Isolation levels formalized
- Snapshot isolation guarantees proved
- Write conflict detection modeled

---

### 3.3 Multi-Stream Transactions

**Objective:** Formalize cross-stream transactional semantics

#### 3.3.1 Transaction Model
- [ ] Define `Transaction` type:
  - List of command executions across multiple streams
  - Atomic commit: all events succeed or all fail
- [ ] Define transaction execution semantics:
  - `execTransaction : Transaction → History → Option History`
  - Returns `none` if any command guard fails
  - Appends all emitted events atomically if successful

#### 3.3.2 Transaction Properties
- [ ] Prove atomicity:
  - `execTransaction tx h = some h'` → all events in `h' \ h` came from `tx`
- [ ] Prove isolation:
  - Concurrent transactions see consistent snapshots
- [ ] Prove durability (abstract):
  - Once committed, events are in history (modulo storage assumptions)

**Acceptance:**
- Transaction model defined
- ACID properties formalized and proved (modulo storage abstraction)
- Multi-stream example transactions in Examples

---

## 4. Typechecker Completeness

### 4.1 Bidirectional Typing

**Objective:** Prove algorithmic typechecker is complete with respect to declarative spec

#### 4.1.1 Strengthen Declarative Typing
- [ ] Remove `byInfer` constructor from `HasType`
- [ ] Add explicit constructors for all Expr forms:
  - Arithmetic: `HasType Γ a tInt → HasType Γ b tInt → HasType Γ (.add a b) tInt`
  - Boolean: `HasType Γ a tBool → HasType Γ b tBool → HasType Γ (.and [a, b]) tBool`
  - Equality: `HasType Γ a t → HasType Γ b t → HasType Γ (.eq a b) tBool`
  - etc.
- [ ] Define typing rules for edge cases:
  - `.eq` with `tDyn` operands
  - `.coalesce` with mixed types
  - `.ifThenElse` with NULL branches

#### 4.1.2 Completeness Theorem
- [ ] **Main Theorem:** `HasType Γ e t → ∃ t', inferExprTy Γ e = some t' ∧ (t' = t ∨ subsumes t' t)`
  - Prove by induction on `HasType` derivation
  - Define `subsumes` relation (e.g., `tDyn` subsumes all types)
- [ ] Prove reverse direction (soundness, already done in v1.5):
  - `inferExprTy Γ e = some t → HasType Γ e t`

#### 4.1.3 Type Inference Decidability
- [ ] Prove `inferExprTy` is computable and terminating (already true, but formalize)
- [ ] Prove type inference is principal:
  - `inferExprTy Γ e = some t → ∀ t', HasType Γ e t' → subsumes t t'`
  - (Most specific type inferred)

**Acceptance:**
- Declarative typing is independent of algorithm
- Bidirectional equivalence proved
- Principal type property proved

---

### 4.2 Type System Extensions

#### 4.2.1 Refinement Types (Optional)
- [ ] Extend `Ty` with refinements:
  - `tIntRange (lo hi : Int)` - bounded integers
  - `tStringPattern (regex : String)` - string constraints
  - `tNonNull t` - non-nullable variant
- [ ] Prove subtyping rules:
  - `tIntRange 0 10 <: tInt`
  - `tNonNull t <: t`
- [ ] Extend typechecker to infer refinements from guards

#### 4.2.2 Dependent Types (Research)
- [ ] Explore dependent types for constraints:
  - `Expr (Γ : TypeEnv) (t : Ty) → HasType Γ e t → TypedExpr Γ t`
  - Type-indexed expressions with correctness by construction
- [ ] Document feasibility and trade-offs

**Acceptance:**
- Refinement types defined (if implemented)
- Subtyping rules proved
- Dependent type exploration documented (research notes)

---

## 5. Bundle Evolution

### 5.1 Migration Composition

**Objective:** Define semantics for multi-step migrations and prove composition properties

#### 5.1.1 Composition Semantics
- [ ] Define `composeMigrations : MigrationSpec → MigrationSpec → MigrationSpec`
  - Chain event transforms: `m1.transform >> m2.transform`
  - Compose state maps: `m2.stateMap ∘ m1.stateMap`
- [ ] Prove composition associativity:
  - `compose (compose m1 m2) m3 = compose m1 (compose m2 m3)`
- [ ] Prove composition respects WFMigration:
  - `WFMigration m1 ir0 ir1 → WFMigration m2 ir1 ir2 → WFMigration (compose m1 m2) ir0 ir2`

#### 5.1.2 Migration Commutativity
- [ ] Define when migrations commute:
  - `MigrationsCommute m1 m2 := ∀ h, migrateHist (compose m1 m2) h = migrateHist (compose m2 m1) h`
- [ ] Prove sufficient conditions for commutativity:
  - Disjoint event types
  - Disjoint state spaces
  - Independent transformations
- [ ] Prove non-commutativity examples (where order matters)

**Acceptance:**
- Composition defined and proved associative
- Commutativity conditions proved
- Multi-step migration example in Examples

---

### 5.2 Rollback and Inverse Migrations

**Objective:** Define migration inverses and prove rollback correctness

#### 5.2.1 Inverse Migration
- [ ] Define `inverseMigration : MigrationSpec → Option MigrationSpec`
  - Swap event transform directions (target → source)
  - Invert state map
  - Return `none` if migration has drops (irreversible)
- [ ] Prove inverse correctness (when defined):
  - `inverseMigration m = some m' → migrateHist (compose m m') h ≈ h` (modulo dropped events)

#### 5.2.2 Partial Rollback
- [ ] Define rollback to intermediate version:
  - Given migrations `m1 : v0 → v1`, `m2 : v1 → v2`, rollback `v2 → v1` via `inverse m2`
- [ ] Prove rollback preserves data (for reversible migrations):
  - No data loss if no drops

**Acceptance:**
- Inverse migration defined
- Rollback correctness proved
- Example: Ticketing v0 → v1 → v0 roundtrip

---

### 5.3 Schema Evolution Patterns

#### 5.3.1 Common Patterns
- [ ] Define and prove correct transformations for:
  - Add field (with default value)
  - Remove field (with drop semantics)
  - Rename field (bijective mapping)
  - Change type (with validation/coercion)
  - Split entity (1 stream → 2 streams)
  - Merge entity (2 streams → 1 stream)

#### 5.3.2 Migration Safety
- [ ] Define `SafeMigration` predicate:
  - No data loss (no drops unless explicit)
  - Type-safe (target schema validates transformed data)
  - Reversible (has valid inverse)
- [ ] Prove safety properties for common patterns

**Acceptance:**
- Common evolution patterns catalogued
- Safety predicates defined
- All patterns proved safe or documented as unsafe

---

## 6. Proof Engineering and Automation

### 6.1 Tactic Library

**Objective:** Build reusable tactics for common proof patterns

#### 6.1.1 Query Reasoning Tactics
- [ ] `query_normalize` - normalize query to canonical form
- [ ] `query_equiv` - prove two queries equivalent via rewrite rules
- [ ] `snap_irrelevant` - discharge irrelevant SnapSet entries

#### 6.1.2 WF Reasoning Tactics
- [ ] `wf_auto` - automatically discharge WFTypeSpec goals from checkTypeSpec
- [ ] `reducer_safe` - prove ReducerPreservesWF from op inspection

#### 6.1.3 Migration Tactics
- [ ] `migration_commute` - prove migration commutativity from structure
- [ ] `roundtrip` - prove inverse migration correctness

**Acceptance:**
- Tactic library exists and is used in Examples
- 50%+ reduction in proof size for common patterns
- Tactics documented in Lean doc comments

---

### 6.2 Verified Code Generation

**Objective:** Generate TypeScript from Lean definitions with correctness guarantees

#### 6.2.1 Code Extraction
- [ ] Define extraction from Lean `def` to TypeScript functions
- [ ] Extract `evalQuery`, `evalExpr`, `holdsConstraint` to TS
- [ ] Prove extracted code matches Lean semantics (via testing or translation validation)

#### 6.2.2 Runtime Verification
- [ ] Generate runtime assertions from `WFTypeSpec`:
  - Check reducer targets declared
  - Check state transitions valid
- [ ] Generate conformance tests from Lean theorems:
  - Test that TS implementation matches Lean oracle on random inputs

**Acceptance:**
- Extraction framework exists (prototype)
- At least one core function extracted and validated
- Path to full extraction documented

---

## 7. Examples and Case Studies

### 7.1 Extended Examples

#### 7.1.1 CRM System
- [ ] Define full CRM schema:
  - Contacts, Companies, Deals, Activities
  - Cross-stream constraints (deal must reference valid contact)
- [ ] Define multi-stream transactions:
  - Create deal + link contact + log activity (atomic)
- [ ] Prove transactional properties:
  - Atomicity: all-or-nothing
  - Isolation: concurrent deal creation doesn't conflict

#### 7.1.2 Kanban Board
- [ ] Extend Kanban with:
  - Board-level constraints (WIP limits via bool_query)
  - Task dependencies (blocked-by relationships)
  - Multi-board views (queries with joins)
- [ ] Prove WIP limit enforcement:
  - Cannot move task if column at capacity
- [ ] Migration example:
  - Add "blocked-by" field to existing boards

#### 7.1.3 Collaborative Document Editing
- [ ] Define CRDT-like reducers:
  - Insert, delete, format operations
  - Concurrent edits with operational transformation
- [ ] Prove convergence:
  - Different replay orders yield same final state (for commutative ops)
- [ ] Prove causality preservation:
  - Happens-before relation matches document history

**Acceptance:**
- All three examples fully formalized
- Properties proved (not just stated)
- Examples demonstrate v2 features (joins, transactions, etc.)

---

## 8. Documentation and Ecosystem

### 8.1 Proof Documentation

- [ ] Generate Lean doc comments for all public definitions
- [ ] Add module-level documentation explaining file organization
- [ ] Create proof roadmap document linking theorems to design goals
- [ ] Document proof strategies and common pitfalls

### 8.2 Integration with TypeScript

- [ ] Document correspondence between Lean and TS implementations:
  - Which TS files correspond to which Lean modules
  - How to keep them in sync
- [ ] Add CI check: Lean build must pass before TS tests run
- [ ] Generate TS types from Lean definitions (aspirational)

### 8.3 Tutorial and Onboarding

- [ ] Write tutorial: "Proving Properties of Your CICSC Bundle"
- [ ] Add worked example: prove custom constraint correct
- [ ] Add FAQ: common Lean/CICSC questions

**Acceptance:**
- Documentation exists and is up-to-date
- External contributor can understand proof structure from docs
- Tutorial can be completed in < 2 hours

---

## v2 Acceptance Checklist

v2 is complete when all are true:

- [ ] **Query Algebra:** Joins, groupBy, aggregations have formal semantics with proved properties
- [ ] **SQL Conformance:** Lowering defined, conformance theorem proved for v1 subset, path to v2 documented
- [ ] **Concurrency:** Happens-before relation formalized, isolation properties proved, multi-stream transactions modeled
- [ ] **Typechecker:** Bidirectional equivalence proved, principal types proved
- [ ] **Migrations:** Composition and rollback semantics defined, safety properties proved
- [ ] **Proof Automation:** Tactic library exists and reduces proof burden by 50%+
- [ ] **Examples:** CRM, Kanban, Document editing fully formalized with properties proved
- [ ] **Documentation:** Proof roadmap, tutorial, and TS integration guide exist

---

## Non-Goals (v3+)

v2 focuses on semantic completeness for core features. The following are deferred:

- **Distributed CICSC:** Multi-node consensus, partition tolerance
- **Performance Verification:** Complexity bounds, query optimization proofs
- **Full SQL Compatibility:** Window functions, CTEs, stored procedures
- **Live Migration:** Zero-downtime cutover with online schema evolution
- **Custom Reducer Verification:** Automated proofs for user-defined reducers (requires SMT/symbolic execution)

---

## Estimated Effort

**Total:** ~6-12 months for experienced Lean developer(s)

| Work Item | Effort | Priority | Dependencies |
|-----------|--------|----------|--------------|
| 1. Full Query Algebra | 8-12 weeks | HIGH | v1.5 complete |
| 2. SQL Conformance | 6-8 weeks | MEDIUM | Item 1 |
| 3. Concurrency Properties | 8-10 weeks | MEDIUM | v1.5 complete |
| 4. Typechecker Completeness | 4-6 weeks | LOW | v1.5 complete |
| 5. Bundle Evolution | 6-8 weeks | MEDIUM | v1.5 complete |
| 6. Proof Engineering | 4-6 weeks | LOW | Items 1-5 (iterative) |
| 7. Examples | 4-6 weeks | HIGH | Items 1-5 |
| 8. Documentation | 2-3 weeks | MEDIUM | Items 1-7 |

**Critical Path:** Item 1 (Query Algebra) → Item 2 (SQL Conformance) → Item 7 (Examples)

**Recommended Order:**
1. Query Algebra (enables everything else)
2. Examples (CRM, Kanban) - drives feature requirements
3. Concurrency + Migrations (parallel work streams)
4. SQL Conformance + Typechecker (polish and rigor)
5. Proof Engineering + Documentation (throughout)

---

## Success Metrics

v2 achieves feature completeness when:

### Quantitative
- **100%** of SQL relational algebra operators have formal semantics (up from ~40% in v1)
- **90%+** conformance test pass rate (Lean oracle vs SQL execution)
- **3+** realistic end-to-end examples fully proved (CRM, Kanban, Docs)
- **50%+** proof size reduction via tactics (compared to manual proofs)

### Qualitative
- **Production-Ready Query Engine:** All CICSC queries can be formally reasoned about
- **SQL Backend Confidence:** Conformance theorem gives strong guarantees about correctness
- **Concurrency Safety:** Transactional properties enable multi-user scenarios
- **Migration Safety:** Schema evolution is provably correct, not ad-hoc
- **Ecosystem Maturity:** External contributors can add proved properties to their bundles

---

## Relationship to Previous Milestones

**v0:** Existence proof - showed naturality theorem was provable
**v1:** Faithful semantics - covered the minimal viable fragment with real replay semantics
**v1.5:** Coherency complete - closed all proof gaps, unified semantic layers
**v2:** Feature complete - full query algebra, SQL conformance, concurrency, migrations
**v3 (future):** Distributed and performant - multi-node, optimization, live migration

---

## Migration Path from v1.5 to v2

### Breaking Changes
- `evalQuery` signature may change to support joins (additional parameters)
- `HasType` loses `byInfer` constructor (proofs must be constructive)
- `MigrationSpec` extended with composition operators

### Compatible Changes
- All v1.5 theorems remain valid (v2 is conservative extension)
- New query operators are opt-in (existing queries still work)
- Concurrency properties are additive (don't invalidate v1.5 proofs)

### Validation
- [ ] All v1.5 Examples still type-check under v2
- [ ] v1.5 acceptance theorems still hold
- [ ] No regression in build time or proof complexity for existing code

---

## Open Research Questions

1. **Query Optimization Correctness:**
   - Can we prove that SQL query optimizer rewrites preserve semantics?
   - Define logical plan vs physical plan distinction

2. **Dependent Types for Schemas:**
   - Use types indexed by IR to enforce well-formedness at compile time
   - `Query (ir : IR) (ts : TypeSpec) → WFTypeSpec ts → ...`

3. **Automated Reducer Verification:**
   - Use symbolic execution or SMT to prove user reducers preserve invariants
   - Generate WFTypeSpec proofs automatically from reducer code

4. **Live Migration:**
   - Model dual-write during migration (old + new schema simultaneously)
   - Prove consistency between old and new representations

5. **Conflict-Free Replicated Data Types (CRDTs):**
   - Formalize CRDT semantics in CICSC framework
   - Prove strong eventual consistency for CRDT-based reducers

---

## Definition of Done (Per Work Item)

Each work item is complete when:

- **Semantics:** Formal definition in Lean (no `sorry`, no TODO)
- **Properties:** Key theorems stated and proved
- **Examples:** At least one realistic example using the feature
- **Tests:** Differential tests (if applicable) pass
- **Docs:** Feature documented in module comments + proof roadmap
- **Integration:** Feature works with existing v1.5 code (no breaking changes without migration path)

---

## Conclusion

v2 transforms the Lean kernel from a coherency-complete proof of concept into a
**feature-complete formal foundation** for CICSC. It enables:

- Reasoning about real-world queries (joins, aggregations, subqueries)
- Trusting the SQL backend (via conformance proofs)
- Building multi-user systems (via concurrency properties)
- Evolving schemas safely (via migration composition and rollback)

After v2, CICSC will have one of the most comprehensive formal semantics of any
application framework, approaching the rigor of verified compilers like CompCert
while remaining practical for building real socio-technical systems.

**North Star:** By v2 completion, a developer should be able to write a CICSC
bundle, prove its key invariants in Lean, and deploy it with high confidence
that the runtime behavior matches the formal specification.
