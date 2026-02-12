import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.ExprEval

namespace Cicsc.Core

def isSnapshotConstraint : Constraint → Bool
  | .snapshot _ _ => true
  | .boolQuery _ _ _ => false

def evalSnapshotConstraint (c : Constraint) (st : State) : Bool :=
  match c with
  | .snapshot _onType expr =>
      toBool (evalExpr {
        now := 0
        actor := ""
        state := st.st
        attrs := st.attrs
        row := st.attrs ++ st.shadows ++ [("state", .vString st.st)]
      } expr)
  | _ => true

def evalQueryRowsCount (_q : Query) (_rows : List State) : Nat :=
  -- v0 abstract placeholder: query semantics are refined separately
  _rows.length

def evalBoolQueryConstraint (c : Constraint) (rows : List State) : Bool :=
  match c with
  | .boolQuery _onType q assertExpr =>
      -- v0 stub: bool_query depends only on row count until Query semantics are formalized.
      let n := evalQueryRowsCount q rows
      toBool (evalExpr {
        now := 0
        actor := ""
        state := ""
        rowsCount := some n
      } assertExpr)
  | _ => true

def holdsConstraint (c : Constraint) (st : State) (rows : List State) : Bool :=
  match c with
  | .snapshot _ _ => evalSnapshotConstraint c st
  | .boolQuery _ _ _ => evalBoolQueryConstraint c rows

def holdsAllConstraints (cs : List (String × Constraint)) (st : State) (rows : List State) : Bool :=
  cs.all (fun kv => holdsConstraint kv.snd st rows)

def holdsAllSnapshotConstraints (cs : List (String × Constraint)) (st : State) : Bool :=
  cs.all (fun kv =>
    match kv.snd with
    | .snapshot _ _ => evalSnapshotConstraint kv.snd st
    | .boolQuery _ _ _ => true)

theorem holdsAllSnapshotConstraints_onlySnapshot
  (cs : List (String × Constraint))
  (st : State) :
  holdsAllSnapshotConstraints cs st =
    (cs.filter (fun kv => isSnapshotConstraint kv.snd)).all (fun kv => evalSnapshotConstraint kv.snd st) := by
  induction cs with
  | nil =>
      simp [holdsAllSnapshotConstraints]
  | cons hd tl ih =>
      cases hd.snd <;> simp [holdsAllSnapshotConstraints, isSnapshotConstraint, ih]

end Cicsc.Core
