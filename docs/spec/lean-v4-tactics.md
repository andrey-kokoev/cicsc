# Lean v4 Tactics (CICSC)

This document records baseline proof automation helpers introduced in v4.

## `query_equiv`

Purpose: normalize row-equivalence goals (`rowsEquiv`, `rowSetEquiv`, `rowSeqEquiv`).

Example:

```lean
theorem rows_refl (rows : List QueryRow) : rowsEquiv false rows rows := by
  query_equiv
```

## `snap_irrelevant`

Purpose: simplify goals involving filtered snapshots and irrelevant snapset entries.

Example:

```lean
theorem snap_irrel_demo (sid : StreamId) (h : History) (e : Event) :
  e ∈ h.filter (inStream sid) → e ∈ h := by
  intro hmem
  snap_irrelevant
```

## `wf_auto`

Purpose: bridge checker booleans to WF propositions (`checkTypeSpec/checkIR`).

Example:

```lean
theorem wf_from_check (ts : TypeSpec) (h : checkTypeSpec ts = true) : WFTypeSpec ts := by
  wf_auto
```

## `migration_simp`

Purpose: simplify migration compose/inverse/rollback expressions.

Example:

```lean
theorem rollback_def_demo (chain : List MigrationSpec) (h : History) :
  rollbackHistory chain h =
    match inverseMigrationChain chain with
    | none => none
    | some inv => some (applyMigrationChain inv h) := by
  migration_simp
```
