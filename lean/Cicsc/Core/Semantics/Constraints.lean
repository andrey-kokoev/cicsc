import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.ExprEval
import Cicsc.Core.Semantics.Replay

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
        row := runtimeRow st
      } expr)
  | _ => true

def evalQueryRowsCount (_q : Query) (_rows : List State) : Nat :=
  -- v0 abstract placeholder: query semantics are refined separately
  _rows.length

-- Experimental v0-only stub. This is not part of proved kernel semantics.
def evalBoolQueryConstraintStub (c : Constraint) (rows : List State) : Bool :=
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

-- Proved kernel semantics (v0): snapshot constraints only.
def holdsKernelConstraint (c : Constraint) (st : State) : Bool :=
  match c with
  | .snapshot _ _ => evalSnapshotConstraint c st
  | .boolQuery _ _ _ => true

def holdsAllKernelConstraints (cs : List (String × Constraint)) (st : State) : Bool :=
  cs.all (fun kv => holdsKernelConstraint kv.snd st)

-- Legacy full surface with bool_query stub. Keep explicitly marked as v0/non-proved.
def holdsConstraintV0 (c : Constraint) (st : State) (rows : List State) : Bool :=
  match c with
  | .snapshot _ _ => evalSnapshotConstraint c st
  | .boolQuery _ _ _ => evalBoolQueryConstraintStub c rows

def holdsAllConstraintsV0 (cs : List (String × Constraint)) (st : State) (rows : List State) : Bool :=
  cs.all (fun kv => holdsConstraintV0 kv.snd st rows)

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
      simp [holdsAllKernelConstraints, holdsKernelConstraint]
  | cons hd tl ih =>
      cases hd.snd <;> simp [holdsAllKernelConstraints, holdsKernelConstraint, isSnapshotConstraint, ih]

end Cicsc.Core
