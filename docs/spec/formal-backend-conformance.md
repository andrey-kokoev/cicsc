# Formal Backend Conformance Specification

> Phase 4: Proof-Backed Field Reliability  
> Document ID: cicsc/spec/formal-backend-conformance-v1  
> Status: Proved / Scoped / Deferred labels applied per P4.1

---

## 1. Scope and Claims

This document defines the conformance relationship between the Lean kernel semantics (oracle) and SQL backend execution.

### 1.1 Proved Claims

Claims with theorem references in `lean/Cicsc/Sql/Conformance.lean`:

| Claim | Theorem | Status |
|-------|---------|--------|
| Row equivalence is an equivalence relation | `rowSetEquiv_refl`, `rowSetEquiv_symm`, `rowSetEquiv_trans` | Proved |
| V4 subset queries are within scope | `execQueryV4_toQuery_in_subset` | Proved |
| SQL lowering conforms for V4 subset | `execSQL_lowerQuery_conforms_execShape` | Proved (scoped) |

### 1.2 Scoped Claims

Claims that hold for explicitly defined subsets:

| Claim | Scope | Status |
|-------|-------|--------|
| SQL conformance | `ExecQueryV4` (snap source + filter/project/offset/limit) | Scoped |
| Expression lowering | Operators in `supportsExprV4` | Scoped |
| Query operators | `supportsQueryOpV4` defined subset | Scoped |

### 1.3 Deferred Claims

Claims not yet established:

| Claim | Deferred To | Reason |
|-------|-------------|--------|
| Full join semantics | Phase 4+ | Complex correlation handling |
| Window functions | Phase 5 | Not in core calculus |
| CTEs (WITH clauses) | Phase 5 | Require recursion analysis |

---

## 2. Conformance Theorem

### 2.1 Main Theorem (Scoped)

```lean
theorem execSQL_lowerQuery_conforms_execShape
  (q : ExecQueryV4)
  (snaps : SnapSet)
  (hFilterExpr : ...)
  (hProjectExpr : ...) :
  rowsEquiv false
    (execSQL (lowerQuery q.toQuery) (dbFromSnapSet q.typeName snaps))
    (evalQuery { version := 0, types := [] } q.toQuery snaps)
```

**Location**: `lean/Cicsc/Sql/Conformance.lean:103-192`

**Scope Restrictions**:
- Source must be `.snap typeName` (no joins)
- Pipeline limited to: filter, project, offset, limit
- Expressions must satisfy `supportsExprV4`

### 2.2 Expression Bridge Hypotheses

The theorem takes bridge hypotheses that must be established separately:

- `hFilterExpr`: Filter expression lowering correctness
- `hProjectExpr`: Projection expression lowering correctness

These are proved per-constructor in `lean/Cicsc/Sql/Lowering.lean`.

---

## 3. Row Equivalence

### 3.1 Definitions

```lean
-- Set equivalence (for unordered queries)
def rowSetEquiv (a b : List QueryRow) : Prop :=
  (∀ r, r ∈ a → r ∈ b) ∧ (∀ r, r ∈ b → r ∈ a)

-- Sequence equivalence (for ordered queries)
def rowSeqEquiv (a b : List QueryRow) : Prop :=
  a = b

-- Conditional equivalence
def rowsEquiv (ordered : Bool) (a b : List QueryRow) : Prop :=
  if ordered then rowSeqEquiv a b else rowSetEquiv a b
```

### 3.2 Properties

| Property | Theorem | Proof |
|----------|---------|-------|
| Reflexivity | `rowSetEquiv_refl` | `constructor <;> intro r hr <;> exact hr` |
| Symmetry | `rowSetEquiv_symm` | `exact ⟨h.2, h.1⟩` |
| Transitivity | `rowSetEquiv_trans` | Standard set transitivity |

---

## 4. V4 Conformance Scope

### 4.1 Supported Query Shape

```lean
structure ExecQueryV4 where
  typeName : TypeName
  filterExpr : Option Expr := none
  projectFields : Option (List ProjectField) := none
  offsetN : Option Nat := none
  limitN : Option Nat := none
```

### 4.2 Supported Expression Operators

| Operator | Lean Eval | SQL Lowering | Status |
|----------|-----------|--------------|--------|
| `eq` | `evalExpr` | `lowerExpr` | Proved |
| `lit` | `evalExpr` | `lowerExpr` | Proved |
| `var:row` | `evalVarRef` | `lowerVarRef` | Proved |
| `and` | `evalAnd` | `SQLAnd` | Proved |
| `or` | `evalOr` | `SQLOr` | Proved |

### 4.3 Explicit Exclusions

Defined in `lean/Cicsc/Core/Semantics/ConformanceScope.lean`:

```lean
def outOfScopeQueryOpForExecTheorem : QueryOp → Bool
  | .join _ _ _ => true
  | .group_by _ => true
  | .having _ => true
  | _ => false
```

---

## 5. Test Infrastructure

### 5.1 Deterministic Replay (P4.2.3)

Conformance tests support deterministic reproduction via replay artifacts:

```typescript
// On failure, artifact is written:
// test-artifacts/conformance/replay-failure-seed-{seed}-{timestamp}.json

// To replay:
CICSC_REPLAY_ARTIFACT=./test-artifacts/conformance/replay-failure-seed-1234.json npm test
```

**Artifact Schema**:
```typescript
type ReplayArtifact = {
  version: "cicsc/conformance-replay-v1"
  generatedAt: string
  seed: number
  query: Query
  snapRows: SnapshotRow[]
  metadata: {
    generatorVersion: string
    schemaType: string
  }
}
```

### 5.2 Coverage Reporting (P4.2.5)

Generate operator coverage report:

```bash
# Generate report
node tests/conformance/operator-coverage-report.ts docs/conformance-coverage.md

# Current coverage: ~75%
# Gaps explicitly documented with priority labels
```

---

## 6. Known Limitations

### 6.1 Semantic Gaps

| Area | Lean Semantics | SQL Semantics | Mitigation |
|------|----------------|---------------|------------|
| NULL handling | Three-valued logic | Three-valued logic | Tested explicitly |
| String collation | Binary | Locale-dependent | Explicit scope restriction |
| Float precision | Exact rationals | IEEE 754 | Avoid in conformance tests |

### 6.2 Unverified Optimizations

The following are not covered by the conformance theorem:

- Query plan optimization (join reordering)
- Index selection
- Parallel execution

---

## 7. Verification Checklist

- [x] Main conformance theorem stated and proved (scoped)
- [x] Row equivalence properties proved
- [x] Expression bridge hypotheses documented
- [x] Explicit exclusions listed
- [x] Replay artifact format defined
- [x] Coverage report generated
- [ ] Full join semantics (deferred)
- [ ] Aggregation semantics in main theorem (deferred)

---

## 8. References

1. **Lean Conformance Module**: `lean/Cicsc/Sql/Conformance.lean`
2. **Scope Definitions**: `lean/Cicsc/Core/Semantics/ConformanceScope.lean`
3. **SQL Lowering**: `lean/Cicsc/Sql/Lowering.lean`
4. **Test Harness**: `tests/conformance/random-oracle-harness.ts`
5. **Coverage Report**: `tests/conformance/operator-coverage-report.ts`
