import Cicsc.Core.Semantics.QueryEval
import Cicsc.Sql.Exec
import Cicsc.Sql.Lowering
import Cicsc.Core.Semantics.ConformanceScope
import Cicsc.Tactics.QueryEquiv

namespace Cicsc.Sql
open Cicsc.Core

def rowSetEquiv (a b : List QueryRow) : Prop :=
  (∀ r, r ∈ a → r ∈ b) ∧ (∀ r, r ∈ b → r ∈ a)

def rowSeqEquiv (a b : List QueryRow) : Prop :=
  a = b

def rowsEquiv (ordered : Bool) (a b : List QueryRow) : Prop :=
  if ordered then rowSeqEquiv a b else rowSetEquiv a b

theorem rowSetEquiv_refl (rows : List QueryRow) : rowSetEquiv rows rows := by
  query_equiv

theorem rowSetEquiv_symm (a b : List QueryRow) : rowSetEquiv a b → rowSetEquiv b a := by
  intro h
  exact ⟨h.2, h.1⟩

theorem rowSetEquiv_trans (a b c : List QueryRow) :
  rowSetEquiv a b → rowSetEquiv b c → rowSetEquiv a c := by
  intro hab hbc
  constructor
  · intro r hra
    exact hbc.1 r (hab.1 r hra)
  · intro r hrc
    exact hab.2 r (hbc.2 r hrc)

theorem rowsEquiv_unordered_refl (rows : List QueryRow) :
  rowsEquiv false rows rows := by
  query_equiv

theorem rowsEquiv_ordered_refl (rows : List QueryRow) :
  rowsEquiv true rows rows := by
  query_equiv

structure ExecQueryV4 where
  typeName : TypeName
  filterExpr : Option Expr := none
  projectFields : Option (List ProjectField) := none
  offsetN : Option Nat := none
  limitN : Option Nat := none
deriving Repr, DecidableEq

def ExecQueryV4.toQuery (q : ExecQueryV4) : Query :=
  let filterOps :=
    match q.filterExpr with
    | none => []
    | some e => [.filter e]
  let projectOps :=
    match q.projectFields with
    | none => []
    | some fs => [.project fs]
  let offsetOps :=
    match q.offsetN with
    | none => []
    | some n => [.offset n]
  let limitOps :=
    match q.limitN with
    | none => []
    | some n => [.limit n]
  {
    source := .snap q.typeName
    pipeline := filterOps ++ projectOps ++ offsetOps ++ limitOps
  }

def dbFromSnapSet (typeName : TypeName) (snaps : SnapSet) : DB :=
  [("snapshots_v0", (lookupSnapRows snaps typeName).map mkRow)]

def evalExecQueryOracle (q : ExecQueryV4) (snaps : SnapSet) : List QueryRow :=
  let base := (lookupSnapRows snaps q.typeName).map mkRow
  let filtered :=
    match q.filterExpr with
    | none => base
    | some e => base.filter (fun r => evalFilterExpr r e)
  let projected :=
    match q.projectFields with
    | none => filtered
    | some fs => filtered.map (fun r => evalProject r fs)
  let dropped :=
    match q.offsetN with
    | none => projected
    | some n => projected.drop n
  match q.limitN with
  | none => dropped
  | some n => dropped.take n

theorem evalExecQueryOracle_eq_evalQuerySubset
  (q : ExecQueryV4)
  (snaps : SnapSet) :
  evalExecQueryOracle q snaps = evalQuerySubset q.toQuery snaps := by
  unfold evalExecQueryOracle ExecQueryV4.toQuery evalQuerySubset evalSourceSubset
  cases hFilter : q.filterExpr <;> cases hProject : q.projectFields <;>
    cases hOffset : q.offsetN <;> cases hLimit : q.limitN <;> simp [hFilter, hProject, hOffset, hLimit, applyQueryOpSubset]

theorem execSQL_lowerQuery_conforms_execShape
  (q : ExecQueryV4)
  (snaps : SnapSet)
  (hFilterExpr :
    ∀ row e, q.filterExpr = some e →
      evalSQLBool row (lowerExpr e) = evalFilterExpr row e)
  (hProjectExpr :
    ∀ row fields pf, q.projectFields = some fields → pf ∈ fields →
      evalSQLExpr row (lowerExpr pf.expr) = evalExpr (rowEnv row) pf.expr) :
  rowsEquiv false
    (execSQL (lowerQuery q.toQuery) (dbFromSnapSet q.typeName snaps))
    (evalQuery { version := 0, types := [] } q.toQuery snaps) := by
  unfold rowsEquiv
  simp [rowSetEquiv]
  have hEvalSubset :
      evalExecQueryOracle q snaps = evalQuerySubset q.toQuery snaps :=
    evalExecQueryOracle_eq_evalQuerySubset q snaps
  have hSqlEqOracle :
      execSQL (lowerQuery q.toQuery) (dbFromSnapSet q.typeName snaps) =
        evalExecQueryOracle q snaps := by
    unfold execSQL dbFromSnapSet lookupTable
    unfold lowerQuery lowerQueryOp
    unfold ExecQueryV4.toQuery evalExecQueryOracle
    cases hFilter : q.filterExpr <;> cases hProject : q.projectFields <;>
      cases hOffset : q.offsetN <;> cases hLimit : q.limitN
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row e he
      exact hFilterExpr row e he
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row e he
      exact hFilterExpr row e he
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row e he
      exact hFilterExpr row e he
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row e he
      exact hFilterExpr row e he
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row fields pf heq hmem
      exact hProjectExpr row fields pf heq hmem
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row fields pf heq hmem
      exact hProjectExpr row fields pf heq hmem
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row fields pf heq hmem
      exact hProjectExpr row fields pf heq hmem
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row fields pf heq hmem
      exact hProjectExpr row fields pf heq hmem
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row e he
      exact hFilterExpr row e he
      intro row fields pf heq hmem
      exact hProjectExpr row fields pf heq hmem
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row e he
      exact hFilterExpr row e he
      intro row fields pf heq hmem
      exact hProjectExpr row fields pf heq hmem
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row e he
      exact hFilterExpr row e he
      intro row fields pf heq hmem
      exact hProjectExpr row fields pf heq hmem
    · simp [hFilter, hProject, hOffset, hLimit, applySelect]
      intro row e he
      exact hFilterExpr row e he
      intro row fields pf heq hmem
      exact hProjectExpr row fields pf heq hmem
  have hEval :
      evalQuery { version := 0, types := [] } q.toQuery snaps =
        evalQuerySubset q.toQuery snaps := by
    unfold evalQuery
    simp [ExecQueryV4.toQuery]
  constructor
  · intro r hr
    rw [hSqlEqOracle] at hr
    rw [hEvalSubset] at hr
    rw [← hEval]
    exact hr
  · intro r hr
    rw [hSqlEqOracle]
    rw [hEvalSubset]
    rw [← hEval] at hr
    exact hr

theorem execQueryV4_toQuery_in_subset
  (q : ExecQueryV4)
  (hFilter :
    match q.filterExpr with
    | none => True
    | some e => supportsExprV4 e = true)
  (hProject :
    match q.projectFields with
    | none => True
    | some fs => supportsProjectFieldsV4 fs = true) :
  QueryV4Subset q.toQuery := by
  unfold QueryV4Subset supportsQueryV4 supportsSourceV4 ExecQueryV4.toQuery
  cases hfe : q.filterExpr <;> cases hpf : q.projectFields <;>
    cases q.offsetN <;> cases q.limitN <;> simp [hfe, hpf, supportsQueryOpV4, hFilter, hProject]

end Cicsc.Sql
