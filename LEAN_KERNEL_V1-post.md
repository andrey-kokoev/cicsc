# LEAN_KERNEL_V1-post.md
## CICSC Lean Kernel v1 → v1.5 Coherency Completion

This document defines the work required to achieve 10/10 coherency with AGENTS.md and LEAN_KERNEL_V1.md objectives.

**Current State:** v1 milestone complete with 8.5/10 coherency
**Target State:** v1.5 with 10/10 coherency - all semantic layers unified, all proofs complete

---

## Coherency Gaps to Address

### Gap 1: Dual Constraint Semantics (Priority: CRITICAL)
**Current Issue:** Two different constraint evaluators with unclear relationship:
- `holdsKernelConstraint` (Constraints.lean:79) - ignores bool_query, returns true
- `holdsConstraintV0` (Constraints.lean:88) - evaluates bool_query via QueryEval

**Violation:** AGENTS.md §5 "Respect the semantic split" - ambiguous which is Core IR truth

**Impact:** Runtime could silently skip bool_query validation if using wrong evaluator

---

### Gap 2: checkIR ↔ WFIR Connection Missing (Priority: HIGH)
**Current Issue:**
- `checkIR` (Typecheck.lean:212) - executable boolean checker
- `WFIR` (WF.lean:76) - Prop-level well-formedness predicate
- No proved connection between them

**Violation:** AGENTS.md §4 "Fail fast at compile-time" - static checks don't guarantee semantic WF

**Impact:** Theorems assume `WFIR`, but runtime uses `checkIR` - potential divergence

---

### Gap 3: Declarative Typing Soundness (Priority: MEDIUM)
**Current Issue:** `HasType` deleted (Typecheck.lean:215 comment), only algorithmic `inferExprTy` exists

**Violation:** AGENTS.md §4 - no semantic definition of "well-typed" independent of algorithm

**Impact:** Cannot prove typechecker correctness, only test it

---

### Gap 4: ReducerPreservesWF is Assumed, Not Proved (Priority: MEDIUM)
**Current Issue:** `ReducerPreservesWF` (Replay.lean:81) is a hypothesis to replay theorems

**Violation:** LEAN_KERNEL_V1.md §4 claims replay preserves WF, but depends on unproven assumption

**Impact:** Well-formedness preservation is conditional, not guaranteed

---

### Gap 5: v0/v1 Naming Confusion (Priority: LOW)
**Current Issue:**
- "v0" in `holdsConstraintV0` unclear (Lean Kernel v0 or IR version 0?)
- Comment at Constraints.lean:78 says "v0" but LEAN_KERNEL_V1 complete

**Violation:** Code hygiene, documentation clarity

**Impact:** Maintainer confusion about versioning scheme

---

## Work Items

### 1. Unify Constraint Semantics

**Objective:** Single canonical constraint evaluator with proved decomposition

Canonical evaluator policy (runtime alignment):
- `holdsConstraint` is the single full-surface evaluator for snapshot + bool_query subset semantics.
- `holdsSnapshotConstraintOnly` is a restricted helper for snapshot-only theorem surfaces.

#### 1.1 Define Canonical Semantics
- [ ] Create `holdsConstraint : IR → Constraint → State → SnapSet → Bool`
  - Handles both snapshot and bool_query constraints
  - Uses QueryEval for bool_query when `supportsQuerySubset`
- [ ] Mark `holdsKernelConstraint` as deprecated or rename to `holdsSnapshotConstraintOnly`
- [ ] Rename `holdsConstraintV0` → `holdsConstraintV1` (align with LEAN_KERNEL_V1)

#### 1.2 Prove Decomposition Properties
- [ ] Theorem: `holdsConstraint ir (.snapshot _ _) st _ = evalSnapshotConstraint ...`
- [ ] Theorem: `holdsConstraint ir (.boolQuery _ q e) _ snaps = evalBoolQueryConstraintSubset ...`
- [ ] Theorem: Constraint holding is independent of out-of-scope SnapSet entries

#### 1.3 Update Downstream Usage
- [ ] Update Examples/QueryConstraints.lean to use canonical evaluator
- [ ] Document which evaluator Runtime/TypeScript should use

**Acceptance:**
- Single source of truth for constraint semantics
- Clear documentation of supported vs unsupported constraint types
- No ambiguity about "which evaluator to use"

---

### 2. Prove checkIR Soundness

**Objective:** Connect executable IR checker to semantic WF predicate

#### 2.1 Prove TypeSpec Connection (Already Exists - Audit)
- [x] `reducerOpsTypecheck_of_checkTypeSpec` exists (WF.lean:81)
- [x] `commandsTypecheck_of_checkTypeSpec` exists (WF.lean:98)
- [x] Audit: Do these cover all of `WFTypeSpec`?

#### 2.2 Prove Missing TypeSpec Properties
- [x] `checkTypeSpecNames ts = true → NoReservedCollisions ts`
- [x] `checkTypeSpecNames ts = true → NoDuplicateFieldNames ts`
- [x] `checkTypeSpec ts = true → initialStateInStates ts`
- [x] `checkTypeSpec ts = true → reducerTargetsDeclared ts`
- [x] `checkTypeSpec ts = true → reducerLiteralStatesValid ts`

#### 2.3 Synthesize Full WFTypeSpec
- [x] Theorem: `checkTypeSpec ts = true → WFTypeSpec ts`
  - Combines all component lemmas

#### 2.4 Prove IR-Level Connection
- [x] Theorem: `checkIR ir = true → WFIR ir`
  - Uses `checkTypeSpec → WFTypeSpec` for each type
  - Proves constraint and view type existence

**Acceptance:**
- `checkIR ir = true → WFIR ir` theorem exists and is proved
- All component lemmas documented
- AGENTS.md §4 "Fail fast at compile-time" principle fully realized

---

### 3. Restore Declarative Typing with Soundness

**Objective:** Separate typechecker specification from algorithm, prove algorithm correct

#### 3.1 Define Declarative Typing Judgment
- [ ] Add `inductive HasType : TypeEnv → Expr → Ty → Prop` in Typecheck.lean
  - Constructors for v1 fragment: lit*, var, .get (with tDyn), .has, boolean ops, arithmetic, conditionals
  - Explicit rule for `.get`: `HasType Γ e tObj → HasType Γ (.get e path) tDyn`
  - Explicit rule for `.var .rowState`: `HasType Γ (.var .rowState) tString`

#### 3.2 Prove Algorithmic Soundness
- [ ] Theorem: `inferExprTy Γ e = some t → HasType Γ e t`
  - Prove by structural induction on Expr
  - May need auxiliary fuel lemma: `inferExprTyFuel Γ (fuel ≥ e.sizeOf) e = some t → HasType Γ e t`

#### 3.3 Document Completeness Gap (Optional for v1.5)
- [ ] Document: `HasType Γ e t` does not imply `inferExprTy Γ e = some t` (completeness)
  - Algorithmic typechecker may be more restrictive than declarative spec
  - This is acceptable for v1.5; completeness is future work

**Acceptance:**
- Declarative `HasType` exists for v1 fragment
- Soundness theorem proved
- Typechecker correctness no longer "tested", it's proved

---

### 4. Make ReducerPreservesWF Explicit

**Objective:** Remove conditional assumption from replay well-formedness theorems

#### 4.1 Option A: Add to WFTypeSpec (Preferred)
- [ ] Extend `WFTypeSpec` with additional conjunct:
  ```lean
  reducerPreservesStates : ∀ (st : State) (e : Event),
    st.st ∈ ts.states →
    (applyReducer ts st e).st ∈ ts.states
  ```
- [ ] Prove this is computable (decidable) for finite state sets
- [ ] Update `checkTypeSpec` to verify this property

#### 4.2 Option B: Prove from Existing WFTypeSpec (Alternative)
- [x] Theorem: `WFTypeSpec ts → ReducerPreservesWF ts`
  - Derive from `reducerLiteralStatesValid` + `reducerOpsTypecheck`
  - May require strengthening `reducerOpsTypecheck` to track state reachability

#### 4.3 Update Replay Theorems
- [ ] Remove `ReducerPreservesWF` hypothesis from theorems
- [ ] Replace with `WFTypeSpec` assumption
- [ ] Update Examples to use unconditional theorems

**Acceptance:**
- No replay theorem assumes `ReducerPreservesWF` as external hypothesis
- Well-formedness preservation is consequence of `WFTypeSpec`
- LEAN_KERNEL_V1.md §4 acceptance criterion fully satisfied

---

### 5. Resolve Versioning Confusion

**Objective:** Clear, consistent naming scheme for Lean kernel versions vs IR versions

#### 5.1 Naming Convention Audit
- [ ] Document distinction:
  - **Lean Kernel Version** (v0, v1, v1.5): Proof completeness milestones
  - **IR Version** (ir.version): Schema version in IR data structure
- [ ] Rename functions with "V0" suffix:
  - `holdsConstraintV0` → `holdsConstraint` (canonical) or `holdsConstraintV1` (if Lean kernel v1 specific)
  - Update comment at Constraints.lean:78 from "v0" to "v1"

#### 5.2 Documentation Updates
- [ ] Add comment header to Constraints.lean explaining evaluator evolution
- [ ] Update LEAN_KERNEL_V1.md §8 checklist to clarify v1 is complete
- [ ] Add forward reference to LEAN_KERNEL_V1-post.md for remaining work

**Acceptance:**
- No ambiguous "v0" references in v1-complete code
- Clear documentation of Lean kernel versions vs IR schema versions
- Maintainers understand "v1.5" is coherency completion, not new features

---

## Acceptance Checklist (v1.5 Complete)

v1.5 is complete when all are true:

- [ ] **Constraint Semantics:** Single canonical `holdsConstraint` evaluator with proved decomposition
- [ ] **Static Discipline:** `checkIR ir = true → WFIR ir` theorem exists and is proved
- [ ] **Typing Soundness:** Declarative `HasType` exists with soundness theorem
- [ ] **WF Completeness:** Replay well-formedness is unconditional consequence of `WFTypeSpec`
- [ ] **Naming Hygiene:** No v0/v1 confusion; clear versioning documentation

---

## Non-Goals (Explicitly Out of Scope for v1.5)

v1.5 focuses on **coherency**, not new features. The following are deferred:

- **Typechecker Completeness:** Proving `HasType Γ e t → ∃ t', inferExprTy Γ e = some t'`
  - Soundness is sufficient for v1.5; completeness is nice-to-have
- **Full Query Algebra:** Joins, groupBy remain unsupported (deferred to v2)
- **SQL Backend Semantics:** Conformance between QueryEval and SQL still TypeScript-level (correct layering)
- **Concurrency Properties:** Still out of scope (v2+)
- **ReducerPreservesWF Automation:** Computing this property is sufficient; automatically deriving it from reducer ops is future work

---

## Estimated Effort

**Total:** ~2-3 weeks for experienced Lean developer

| Work Item | Effort | Priority | Blocking |
|-----------|--------|----------|----------|
| 1. Unify Constraint Semantics | 3-4 days | CRITICAL | None |
| 2. Prove checkIR Soundness | 5-7 days | HIGH | None |
| 3. Declarative Typing | 3-4 days | MEDIUM | None |
| 4. ReducerPreservesWF | 2-3 days | MEDIUM | Item 2 (if Option B) |
| 5. Versioning Cleanup | 1 day | LOW | Item 1 |

**Recommended Order:**
1. Item 1 (fixes critical ambiguity)
2. Item 2 (hardest, most valuable)
3. Item 5 (cleanup while Item 2 fresh in mind)
4. Item 4 (builds on WFTypeSpec understanding from Item 2)
5. Item 3 (independent, can be done anytime)

---

## Success Metrics

v1.5 achieves 10/10 coherency when:

### Quantitative
- **0** dual evaluators with unclear semantics (down from 1)
- **100%** of executable checks (`checkIR`) have proved soundness (up from ~60%)
- **0** replay theorems with unproven assumptions (down from 1)
- **0** algorithmic type systems without declarative specs (down from 1)

### Qualitative
- **Core IR as Single Source of Truth:** No ambiguity about "which function to call"
- **Static Discipline Complete:** Runtime checks guaranteed by compile-time proofs
- **Proof Obligations Explicit:** No hidden assumptions in theorem statements
- **AGENTS.md Alignment:** Perfect score on all 6 principles

---

## Relationship to LEAN_KERNEL_V1.md

**v1 (LEAN_KERNEL_V1.md):**
- ✅ Faithfulness: Core semantics match TypeScript runtime intent
- ✅ Coverage: All v1 fragment features have semantics
- ✅ Evolution: Naturality theorem proved

**v1.5 (this document):**
- 🎯 Coherency: Eliminate semantic ambiguities
- 🎯 Completeness: Close proof gaps
- 🎯 Rigor: Prove everything assumed in v1

**v2 (future):**
- Full Query algebra (joins, groupBy)
- SQL backend semantics
- Concurrency properties
- Full typechecker completeness

---

## Migration Path

For users currently depending on v1:

### Breaking Changes
- `holdsConstraintV0` → `holdsConstraint` (rename)
- Theorems using `ReducerPreservesWF` hypothesis → use `WFTypeSpec` instead

### Compatible Changes
- `checkIR` still works identically (but now has soundness proof)
- `inferExprTy` still works identically (but now has declarative spec)
- All Examples still compile (updated to use new names)

### Validation
- [ ] All Examples type-check with v1.5
- [ ] No change to evalExpr, evalQuery, or applyReducer semantics (pure refactor)
- [ ] lakefile.lean builds cleanly

---

## Documentation Requirements

When v1.5 is complete:

- [ ] Update LEAN_KERNEL_V1.md §8 checklist to reference v1.5 completion
- [ ] Add comments in code referencing relevant LEAN_KERNEL_V1-post.md sections
- [ ] Update README (if exists) with v1.5 status
- [ ] Add migration guide for users updating from v1 to v1.5
- [ ] Update AGENTS.md to reference Lean kernel v1.5 as "coherency complete"

---

## Definition of Done (Per Work Item)

Each work item is complete when:

- **Code:** Lean definitions/theorems written and type-check
- **Proofs:** All theorems proved (no `sorry`)
- **Tests:** At least one example using the new definitions/theorems
- **Docs:** Comments in code explaining the definitions
- **Integration:** Existing Examples still type-check (non-breaking or explicitly breaking)

---

## Open Questions (To Resolve During Work)

1. **ReducerPreservesWF:** Option A (extend WFTypeSpec) vs Option B (derive from existing)?
   - **Recommendation:** Start with Option B; fall back to Option A if derivation impossible

2. **Declarative Typing:** Should `HasType` allow more programs than `inferExprTy` (soundness only) or exactly the same (soundness + completeness)?
   - **Recommendation:** Soundness only for v1.5 (easier); completeness is v2

3. **Constraint Naming:** `holdsConstraint` vs `holdsConstraintV1` vs `evalConstraint`?
   - **Recommendation:** `holdsConstraint` (canonical, no version suffix) + deprecate old names

4. **checkIR Soundness:** Should we also prove `WFIR ir → ∃ witness, checkIR ir = true` (completeness)?
   - **Recommendation:** Soundness only for v1.5; completeness is bonus if easy

---

## Risk Mitigation

### Risk: Proofs harder than estimated
- **Mitigation:** Start with Item 1 (easiest); build proof patterns before Item 2 (hardest)
- **Fallback:** Document gaps as "assumptions" with TODO; v1.5 is still improvement over v1

### Risk: Breaking changes disrupt users
- **Mitigation:** All renames are mechanical; provide sed/grep migration script
- **Fallback:** Offer compatibility shims (type aliases) for deprecated names

### Risk: Option B (derive ReducerPreservesWF) impossible
- **Mitigation:** Have Option A (extend WFTypeSpec) ready as backup
- **Impact:** Minor - either approach satisfies acceptance criteria

---

## Post-v1.5: Toward v2

After achieving 10/10 coherency, next priorities:

1. **Full Query Algebra:** Joins, groupBy semantics
2. **SQL Conformance:** Prove TypeScript SQL lowering matches QueryEval
3. **Concurrency:** Prove transactional isolation properties
4. **Typechecker Completeness:** Prove `HasType` and `inferExprTy` equivalent
5. **Automated Verification:** Generate `checkIR` from `WFIR` (correct by construction)

These are **feature additions** (v2+), not coherency fixes (v1.5).

---

## Appendix: Coherency Scorecard

| Dimension | v1 Score | v1.5 Target | Key Improvement |
|-----------|----------|-------------|-----------------|
| Semantic Unity | 7/10 | 10/10 | Single constraint evaluator |
| Static Discipline | 6/10 | 10/10 | checkIR soundness proved |
| Proof Rigor | 8/10 | 10/10 | No unproven assumptions |
| Type Safety | 7/10 | 10/10 | Declarative typing soundness |
| Documentation | 9/10 | 10/10 | Clear versioning, no ambiguity |
| AGENTS.md §1-6 | 8/10 | 10/10 | All principles fully satisfied |
| **Overall** | **8.5/10** | **10/10** | Production-ready kernel |
