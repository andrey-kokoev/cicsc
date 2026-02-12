# LEAN_KERNEL_V4.md
## CICSC Lean Kernel v4 Plan

This document replaces checklist-completion framing with outcome-completion framing.
Each milestone is complete only when its acceptance criteria are met with concrete proof/test artifacts.

---

## Objective

Deliver a Lean kernel that supports:
- end-to-end SQL-vs-oracle semantic conformance for the supported surface,
- concurrency/isolation semantics with proved safety properties,
- migration algebra (compose/invert/rollback) with correctness conditions,
- typechecker completeness for the declared fragment,
- reusable proof automation for ongoing evolution.

---

## Milestone K4.1: Conformance Theorem Closure

### Outcome
Prove that SQL lowering/execution matches kernel query semantics for the scoped v4 surface.

### TODOs
- [x] K4.1.1 Define a canonical scoped query subset `QueryV4Subset`.
  - Implemented in `lean/Cicsc/Core/Semantics/ConformanceScope.lean` via
    `supportsExprV4`, `supportsSourceV4`, `supportsQueryOpV4`, and `QueryV4Subset`.
- [x] K4.1.2 Prove `lowerExpr` correctness for each expression constructor in scope.
  - Constructor-preservation correctness theorems added in `lean/Cicsc/Sql/Lowering.lean`
    for all currently scoped expression forms.
- [x] K4.1.3 Prove `lowerQuery` correctness for source/filter/project/order/limit/group/having in scope.
  - Operation-level lowering correctness lemmas added for
    `filter/project/groupBy/having/orderBy/limit/offset` and base-query construction.
- [x] K4.1.4 Define row equivalence relation (modulo ordering where applicable).
  - Added `rowSetEquiv`, `rowSeqEquiv`, and `rowsEquiv` in `lean/Cicsc/Sql/Conformance.lean`.
- [x] K4.1.5 State and prove main theorem:
  `execSQL (lowerQuery q) db ≈ evalQuery ir q (snapFromDB db)` for `q ∈ QueryV4Subset`.
  - Added scoped theorem `execSQL_lowerQuery_conforms_execShape` in
    `lean/Cicsc/Sql/Conformance.lean` over executable v4 shape
    (`snap` source + `filter/project/offset/limit`) with explicit expression-bridge hypotheses.
- [x] K4.1.6 Add explicit theorem exclusions list for out-of-scope operators.
  - Added explicit exclusion predicates and specs:
    `outOfScopeQueryOpForExecTheorem`, `outOfScopeExprForExecTheorem`,
    `outOfScopeQueryOpForExecTheorem_spec`, and `outOfScopeExprForExecTheorem_spec`
    in `lean/Cicsc/Core/Semantics/ConformanceScope.lean`.

### Acceptance
- [ ] Main conformance theorem compiles without `sorry`.
- [ ] Differential generated tests pass for all in-scope operators.
- [ ] Theorem and scope are documented in `docs/spec/formal-backend-conformance.md`.

---

## Milestone K4.2: Replay and Causality Theorems

### Outcome
Make replay-causality statements semantically aligned with stream-aware replay and prove core properties.

### TODOs
- [x] K4.2.1 Connect `isCausal` with `Core.Semantics.Replay.replay` via explicit bridge lemmas.
  - Added `lean/Cicsc/Core/Semantics/CausalityReplay.lean` with stream-filter bridge lemmas:
    `mem_streamFilter_iff`, `sameStream_of_inStream_true_true`,
    `isCausal_implies_appearsBefore_in_replayStream`,
    and `replay_stream_events_respect_causal_order`.
- [x] K4.2.2 Prove replay respects happens-before for same-stream events.
  - Added `appearsBefore_filter_preserved` and
    `replay_stream_preserves_happensBefore_order` in
    `lean/Cicsc/Core/Semantics/CausalityReplay.lean`.
- [x] K4.2.3 Define concurrency commutativity premise for reducers (`CommutesOnConcurrent`).
  - Added `concurrent`, `CommutesOnConcurrent`, and `concurrent_symm` in
    `lean/Cicsc/Core/Semantics/CausalityReplay.lean`.
- [x] K4.2.4 Prove replay order independence under `CommutesOnConcurrent`.
  - Added `replayFold_swap_adjacent_concurrent` in
    `lean/Cicsc/Core/Semantics/CausalityReplay.lean` (adjacent swap lemma).
- [x] K4.2.5 Prove deterministic replay for causally-equivalent histories.
  - Added `CausallyEquivalent` plus
    `replayFold_causallyEquivalent` and
    `replay_deterministic_on_causallyEquivalent_streams`
    in `lean/Cicsc/Core/Semantics/CausalityReplay.lean`.

### Acceptance
- [ ] No replay-causality theorem relies on unstated semantic mismatch.
- [ ] All causality theorems reference stream identity (`tenantId/entityType/entityId`) explicitly.

---

## Milestone K4.3: Isolation and Transaction Semantics

### Outcome
Formalize transaction visibility/isolation semantics and prove baseline guarantees.

### TODOs
- [x] K4.3.1 Define `snapshotAt` over history for stream/state lookup.
  - Added `visibleAtSeq` and `snapshotAt` in
    `lean/Cicsc/Core/Semantics/Isolation.lean`.
- [x] K4.3.2 Define `IsolationLevel := ReadCommitted | Snapshot | Serializable`.
  - Added `IsolationLevel` in `lean/Cicsc/Core/Semantics/Isolation.lean`.
- [x] K4.3.3 Define transaction model and execution relation over history.
  - Added `Transaction`, `readCutoff`, `readSnapshot`, `appendWrites`, and `TxExecRel`
    in `lean/Cicsc/Core/Semantics/Isolation.lean`.
- [x] K4.3.4 Prove no dirty reads and non-repeatable-read exclusion for Snapshot.
  - Added `snapshot_no_dirty_reads` and `snapshot_repeatable_reads` in
    `lean/Cicsc/Core/Semantics/Isolation.lean`.
- [x] K4.3.5 Define write-write conflict condition and prove abort-or-serialize property.
  - Added `writeWriteConflict`, `TxConflictOutcome`, `resolveWriteWriteConflict`,
    and `writeWrite_conflict_abort_or_serialize` in
    `lean/Cicsc/Core/Semantics/Isolation.lean`.
- [x] K4.3.6 Provide at least one multi-stream transaction proof example.
  - Added `snapshotAt_ignores_other_stream_writes` in
    `lean/Cicsc/Core/Semantics/Isolation.lean`.

### Acceptance
- [ ] Isolation semantics compile and are used by at least one example theorem.
- [ ] Conflict theorem includes explicit preconditions and failure mode.

---

## Milestone K4.4: Migration Algebra and Safety

### Outcome
Upgrade migration layer from operational transforms to proved algebraic behavior.

### TODOs
- [ ] K4.4.1 Prove associativity of `composeMigrations` under explicit compatibility assumptions.
- [ ] K4.4.2 Define migration commutativity predicate and sufficient conditions.
- [ ] K4.4.3 Implement `inverseMigration` for reversible subset.
- [ ] K4.4.4 Prove roundtrip property for reversible migrations.
- [ ] K4.4.5 Define rollback semantics for multi-step version chains.
- [ ] K4.4.6 Define `SafeMigration` and prove safety for add/rename/remove basic patterns.

### Acceptance
- [ ] At least one nontrivial migration chain has compose + inverse + rollback theorems.
- [ ] Unsafe patterns are explicitly marked and rejected or documented.

---

## Milestone K4.5: Typechecker Completeness for Declared Fragment

### Outcome
Close bidirectional typing for a clearly-scoped expression fragment.

### TODOs
- [ ] K4.5.1 Freeze fragment definition `TypingV4Fragment`.
- [ ] K4.5.2 Align declarative `HasType` constructors with all fragment constructs.
- [ ] K4.5.3 Prove inference soundness for the fragment (if not already complete).
- [ ] K4.5.4 Prove inference completeness up to subsumption (`subsumes`).
- [ ] K4.5.5 Prove principal type property for the fragment.
- [ ] K4.5.6 Document excluded constructs and reasons.

### Acceptance
- [ ] Fragment has soundness + completeness + principality theorems.
- [ ] No theorem depends on `byInfer`-style shortcut rules.

---

## Milestone K4.6: Proof Automation Baseline

### Outcome
Reduce proof maintenance overhead with focused tactics for repeated proof patterns.

### TODOs
- [ ] K4.6.1 Add `query_equiv` tactic for row-equivalence goals.
- [ ] K4.6.2 Add `snap_irrelevant` tactic for irrelevant snapset entries.
- [ ] K4.6.3 Add `wf_auto` bridge tactic from checker booleans to WF props.
- [ ] K4.6.4 Add migration tactic helpers for compose/roundtrip proofs.
- [ ] K4.6.5 Convert at least 5 existing long proofs to tactic-assisted versions.

### Acceptance
- [ ] Demonstrated reduction in proof script size on representative targets.
- [ ] Tactics documented with usage examples.

---

## Milestone K4.7: Kernel Truth and Governance

### Outcome
Prevent checkbox drift by enforcing theorem-indexed completion standards.

### TODOs
- [ ] K4.7.1 Add theorem index section at end of this document.
- [ ] K4.7.2 For each completed item, require file+theorem references.
- [ ] K4.7.3 Add “Scoped Completion” tags where full generality is deferred.
- [ ] K4.7.4 Add CI check that rejects `[x]` items missing references.

### Acceptance
- [ ] Every checked item has verifiable artifact references.
- [ ] No milestone is marked complete on documentation-only basis.

---

## Exit Criteria (Kernel v4)

- [ ] Conformance theorem is proved for `QueryV4Subset`.
- [ ] Replay-causality and deterministic replay theorems are stream-aligned.
- [ ] Isolation and transaction core guarantees are formalized and proved.
- [ ] Migration compose/inverse/rollback theorems are present for scoped subset.
- [ ] Typing fragment has soundness/completeness/principality.
- [ ] Proof automation baseline is operational and adopted.
- [ ] This document has theorem-indexed completion entries only.
