import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.ExprEval
import Cicsc.Core.Semantics.Replay

namespace Cicsc.Core

abbrev QueryRow := List (String × Val)

def rowStateValue (row : QueryRow) : String :=
  match lookupField row "state" with
  | .vString s => s
  | _ => ""

def rowEnv (row : QueryRow) : Env := {
  now := 0
  actor := ""
  state := rowStateValue row
  row := row
}

def evalFilterExpr (row : QueryRow) (e : Expr) : Bool :=
  toBool (evalExpr (rowEnv row) e)

def evalProjectField (row : QueryRow) (pf : ProjectField) : (String × Val) :=
  (pf.name, evalExpr (rowEnv row) pf.expr)

def evalProject (row : QueryRow) (fields : List ProjectField) : QueryRow :=
  fields.map (evalProjectField row)

def orderKeyVal (row : QueryRow) (k : OrderKey) : Val :=
  evalExpr (rowEnv row) k.expr

def valLt (a b : Val) : Bool :=
  match a, b with
  | .vInt x, .vInt y => x < y
  | .vString x, .vString y => x < y
  | .vBool x, .vBool y => x = false && y = true
  | _, _ => false

def rowLtByKeys : List OrderKey → QueryRow → QueryRow → Bool
  | [], _, _ => false
  | k :: ks, a, b =>
      let va := orderKeyVal a k
      let vb := orderKeyVal b k
      if valEq va vb then
        rowLtByKeys ks a b
      else if k.asc then
        valLt va vb
      else
        valLt vb va

def insertSorted (ks : List OrderKey) (x : QueryRow) : List QueryRow → List QueryRow
  | [] => [x]
  | y :: ys =>
      if rowLtByKeys ks x y then
        x :: y :: ys
      else
        y :: insertSorted ks x ys

def sortRows (ks : List OrderKey) (rows : List QueryRow) : List QueryRow :=
  rows.foldl (fun acc r => insertSorted ks r acc) []

def applyQueryOpSubset : QueryOp → List QueryRow → List QueryRow
  | .filter e, rows => rows.filter (fun r => evalFilterExpr r e)
  | .project fields, rows => rows.map (fun r => evalProject r fields)
  | .groupBy _ _, rows => rows
  | .orderBy keys, rows => sortRows keys rows
  | .limit n, rows => rows.take n
  | .offset n, rows => rows.drop n

def supportsQueryOpSubset : QueryOp → Bool
  | .filter _ => true
  | .project _ => true
  | .groupBy _ _ => false
  | .orderBy _ => true
  | .limit _ => true
  | .offset _ => true

def evalSourceSubset (src : Source) (rows : List State) : List QueryRow :=
  match src with
  | .snap _ => rows.map mkRow
  | .slaStatus _ _ => []
  | .join _ _ _ _ => []

def supportsSourceSubset : Source → Bool
  | .snap _ => true
  | _ => false

def supportsQuerySubset (q : Query) : Bool :=
  supportsSourceSubset q.source && q.pipeline.all supportsQueryOpSubset

def evalQuerySubset (q : Query) (rows : List State) : List QueryRow :=
  q.pipeline.foldl (fun acc op => applyQueryOpSubset op acc) (evalSourceSubset q.source rows)

end Cicsc.Core
