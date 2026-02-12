import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.ExprEval
import Cicsc.Core.Semantics.Replay
import Cicsc.Core.Semantics.QueryEval

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
        row := mkRow st
      } expr)
  | _ => true

-- bool_query semantics over the supported relational query subset.
def evalBoolQueryConstraintSubset (ir : IR) (c : Constraint) (rows : List State) : Bool :=
  match c with
  | .boolQuery _onType q assertExpr =>
      if supportsQuerySubset q then
        let n := (evalQuery ir q rows).length
        toBool (evalExpr {
          now := 0
          actor := ""
          state := ""
          rowsCount := some n
        } assertExpr)
      else
        false
  | _ => true

-- Proved kernel semantics (v0): snapshot constraints only.
def holdsKernelConstraint (c : Constraint) (st : State) : Bool :=
  match c with
  | .snapshot _ _ => evalSnapshotConstraint c st
  | .boolQuery _ _ _ => true

def holdsAllKernelConstraints (cs : List (String × Constraint)) (st : State) : Bool :=
  cs.all (fun kv => holdsKernelConstraint kv.snd st)

-- Legacy full surface including bool_query subset semantics.
def holdsConstraintV0 (ir : IR) (c : Constraint) (st : State) (rows : List State) : Bool :=
  match c with
  | .snapshot _ _ => evalSnapshotConstraint c st
  | .boolQuery _ _ _ => evalBoolQueryConstraintSubset ir c rows

def holdsAllConstraintsV0 (ir : IR) (cs : List (String × Constraint)) (st : State) (rows : List State) : Bool :=
  cs.all (fun kv => holdsConstraintV0 ir kv.snd st rows)

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
