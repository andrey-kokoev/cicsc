import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.QueryEval
import Cicsc.Core.Semantics.Constraints

namespace Cicsc.Examples
open Cicsc.Core

def qcType : TypeSpec := {
  idType := "string"
  states := ["open", "closed"]
  initialState := "open"
  attrs := []
  shadows := []
  commands := []
  reducer := [("created", [])]
}

def qcIr : IR := {
  version := 1
  types := [("Ticket", qcType)]
}

def qcRows : List State := [
  { st := "open", attrs := [], shadows := [] },
  { st := "closed", attrs := [], shadows := [] }
]

def openOnlyQuery : Query := {
  source := .snap "Ticket"
  pipeline := [
    .filter (.eq (.var .rowState) (.litString "open")),
    .limit 10
  ]
}

def openCountPositive : Constraint :=
  .boolQuery "Ticket" openOnlyQuery (.gt (.var .rowsCount) (.litInt 0))

theorem boolQuery_subset_example_true :
  holdsConstraintV0 qcIr openCountPositive { st := "open", attrs := [], shadows := [] } qcRows = true := by
  decide

end Cicsc.Examples
