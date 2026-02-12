import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.ExprEval
import Cicsc.Core.Semantics.Replay
import Cicsc.Core.Semantics.QueryEval

namespace Cicsc.Core

def isSnapshotConstraint : Constraint → Bool
  | .snapshot _ _ => true
  | .boolQuery _ _ _ => false

def snapshotEnv (st : State) : Env := {
  now := 0
  actor := ""
  state := st.st
  attrs := st.attrs
  row := mkRow st
}

def assertExprRowsCountArgsOnly : Expr → Bool
  | .litBool _ => true
  | .litInt _ => true
  | .litString _ => true
  | .litNull => true
  | .var (.rowsCount) => true
  | .var (.arg _) => true
  | .var _ => false
  | .get e _ => assertExprRowsCountArgsOnly e
  | .has e _ => assertExprRowsCountArgsOnly e
  | .not e => assertExprRowsCountArgsOnly e
  | .and xs => xs.all assertExprRowsCountArgsOnly
  | .or xs => xs.all assertExprRowsCountArgsOnly
  | .eq a b
  | .ne a b
  | .lt a b
  | .le a b
  | .gt a b
  | .ge a b
  | .add a b
  | .sub a b
  | .mul a b
  | .div a b => assertExprRowsCountArgsOnly a && assertExprRowsCountArgsOnly b
  | .ifThenElse c t f =>
      assertExprRowsCountArgsOnly c && assertExprRowsCountArgsOnly t && assertExprRowsCountArgsOnly f
  | .coalesce xs => xs.all assertExprRowsCountArgsOnly
  | .call _ args => args.all assertExprRowsCountArgsOnly

def evalSnapshotConstraint (c : Constraint) (st : State) : Bool :=
  match c with
  | .snapshot _onType expr =>
      toBool (evalExpr (snapshotEnv st) expr)
  | _ => true

theorem snapshotEnv_usesStateRowAttrs
  (st : State) :
  (snapshotEnv st).state = st.st ∧
  (snapshotEnv st).attrs = st.attrs ∧
  (snapshotEnv st).row = mkRow st := by
  simp [snapshotEnv]

-- bool_query semantics over the supported relational query subset.
def evalBoolQueryConstraintSubset (ir : IR) (c : Constraint) (snaps : SnapSet) : Bool :=
  match c with
  | .boolQuery _onType q assertExpr =>
      if supportsQuerySubset q && assertExprRowsCountArgsOnly assertExpr then
        let n := (evalQuery ir q snaps).length
        toBool (evalExpr {
          now := 0
          actor := ""
          state := ""
          rowsCount := some n
        } assertExpr)
      else
        false
  | _ => true

-- Canonical constraint evaluator for the v1.5 kernel surface.
def holdsConstraint (ir : IR) (c : Constraint) (st : State) (snaps : SnapSet) : Bool :=
  match c with
  | .snapshot _ _ => evalSnapshotConstraint c st
  | .boolQuery _ _ _ => evalBoolQueryConstraintSubset ir c snaps

-- Snapshot-only evaluator used by the proved snapshot constraint surface.
def holdsSnapshotConstraintOnly (c : Constraint) (st : State) : Bool :=
  match c with
  | .snapshot _ _ => evalSnapshotConstraint c st
  | .boolQuery _ _ _ => true

def holdsAllKernelConstraints (cs : List (String × Constraint)) (st : State) : Bool :=
  cs.all (fun kv => holdsSnapshotConstraintOnly kv.snd st)

def holdsAllConstraints (ir : IR) (cs : List (String × Constraint)) (st : State) (snaps : SnapSet) : Bool :=
  cs.all (fun kv => holdsConstraint ir kv.snd st snaps)

def holdsAllSnapshotConstraints (cs : List (String × Constraint)) (st : State) : Bool :=
  cs.all (fun kv =>
    match kv.snd with
    | .snapshot _ _ => evalSnapshotConstraint kv.snd st
    | .boolQuery _ _ _ => true)

theorem holdsAllKernelConstraints_onlySnapshot
  (cs : List (String × Constraint))
  (st : State) :
  holdsAllKernelConstraints cs st =
    (cs.filter (fun kv => isSnapshotConstraint kv.snd)).all (fun kv => evalSnapshotConstraint kv.snd st) := by
  induction cs with
  | nil =>
      simp [holdsAllKernelConstraints, holdsSnapshotConstraintOnly]
  | cons hd tl ih =>
      cases hd.snd <;> simp [holdsAllKernelConstraints, holdsSnapshotConstraintOnly, isSnapshotConstraint, ih]

end Cicsc.Core
