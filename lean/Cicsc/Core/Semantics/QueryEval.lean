import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.ExprEval
import Cicsc.Core.Semantics.Replay

namespace Cicsc.Core

abbrev QueryRow := List (String × Val)
abbrev SnapSet := List (TypeName × List State)

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

theorem rowEnv_usesRowAndState
  (row : QueryRow) :
  (rowEnv row).row = row ∧ (rowEnv row).state = rowStateValue row := by
  simp [rowEnv]

def evalFilterExpr (row : QueryRow) (e : Expr) : Bool :=
  toBool (evalExpr (rowEnv row) e)

def evalProjectField (row : QueryRow) (pf : ProjectField) : (String × Val) :=
  (pf.name, evalExpr (rowEnv row) pf.expr)

def evalProject (row : QueryRow) (fields : List ProjectField) : QueryRow :=
  fields.map (evalProjectField row)

def orderKeyVal (row : QueryRow) (k : OrderKey) : Val :=
  evalExpr (rowEnv row) k.expr

def valLt (a b : Val) : Bool :=
  -- Structural total order over Val (not SQL collation/NULLS mode semantics).
  compare a b = Ordering.lt

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

def lookupSnapRows (snaps : SnapSet) (typeName : TypeName) : List State :=
  match snaps.find? (fun kv => kv.fst = typeName) with
  | some kv => kv.snd
  | none => []

-- v2: Row combination for joins
-- See LEAN_KERNEL_V2.md §1.1.1
-- Combines two query rows by concatenating their field lists.
-- In case of field name collision, left row fields take precedence.
def combineRows (left right : QueryRow) : QueryRow :=
  let rightFiltered := right.filter (fun kv => !left.any (fun lkv => lkv.fst = kv.fst))
  left ++ rightFiltered

-- v2: Join evaluation
-- See LEAN_KERNEL_V2.md §1.1.1
-- Evaluates a join between two lists of rows based on join type and condition.
def evalJoin (joinType : JoinType) (leftRows rightRows : List QueryRow) (condition : Expr) : List QueryRow :=
  match joinType with
  | .cross =>
      -- Cross join: Cartesian product (condition ignored)
      leftRows.flatMap (fun l => rightRows.map (fun r => combineRows l r))
  | .inner =>
      -- Inner join: Cartesian product filtered by condition
      leftRows.flatMap (fun l =>
        rightRows.filterMap (fun r =>
          let combined := combineRows l r
          if evalFilterExpr combined condition then some combined else none))
  | .leftOuter =>
      -- Left outer join: all left rows, with matching right rows or nulls
      leftRows.flatMap (fun l =>
        let matches := rightRows.filterMap (fun r =>
          let combined := combineRows l r
          if evalFilterExpr combined condition then some combined else none)
        if matches.isEmpty then [l] else matches)
  | .rightOuter =>
      -- Right outer join: all right rows, with matching left rows or nulls
      rightRows.flatMap (fun r =>
        let matches := leftRows.filterMap (fun l =>
          let combined := combineRows l r
          if evalFilterExpr combined condition then some combined else none)
        if matches.isEmpty then [r] else matches)
  | .fullOuter =>
      -- Full outer join: all rows from both sides, with nulls for non-matches
      let leftWithMatches := leftRows.flatMap (fun l =>
        let matches := rightRows.filterMap (fun r =>
          let combined := combineRows l r
          if evalFilterExpr combined condition then some combined else none)
        if matches.isEmpty then [l] else matches)
      let unmatchedRight := rightRows.filter (fun r =>
        !leftRows.any (fun l =>
          let combined := combineRows l r
          evalFilterExpr combined condition))
      leftWithMatches ++ unmatchedRight

theorem lookupSnapRows_cons_ne
  (snaps : SnapSet)
  (typeName otherType : TypeName)
  (rows : List State)
  (hne : otherType ≠ typeName) :
  lookupSnapRows ((otherType, rows) :: snaps) typeName = lookupSnapRows snaps typeName := by
  simp [lookupSnapRows, hne]

-- v2: Recursive source evaluation with join support
-- See LEAN_KERNEL_V2.md §1.1.1
partial def evalSourceSubset (src : Source) (snaps : SnapSet) : List QueryRow :=
  match src with
  | .snap typeName => (lookupSnapRows snaps typeName).map mkRow
  | .slaStatus _ _ => []
  | .join joinType left right condition =>
      let leftRows := evalSourceSubset left snaps
      let rightRows := evalSourceSubset right snaps
      evalJoin joinType leftRows rightRows condition

def supportsSourceSubset : Source → Bool
  | .snap _ => true
  | .join _ left right _ => supportsSourceSubset left && supportsSourceSubset right
  | _ => false

def supportsQuerySubset (q : Query) : Bool :=
  supportsSourceSubset q.source && q.pipeline.all supportsQueryOpSubset

def evalQuerySubset (q : Query) (snaps : SnapSet) : List QueryRow :=
  q.pipeline.foldl (fun acc op => applyQueryOpSubset op acc) (evalSourceSubset q.source snaps)

def evalQuery (_ir : IR) (q : Query) (snaps : SnapSet) : List QueryRow :=
  evalQuerySubset q snaps

def evalQueryOpsOracle : List QueryOp → List QueryRow → List QueryRow
  | [], rows => rows
  | op :: ops, rows => evalQueryOpsOracle ops (applyQueryOpSubset op rows)

def oracleQueryEvalSubset (q : Query) (snaps : SnapSet) : List QueryRow :=
  evalQueryOpsOracle q.pipeline (evalSourceSubset q.source snaps)

theorem evalQueryOpsOracle_eq_foldl
  (ops : List QueryOp)
  (rows : List QueryRow) :
  evalQueryOpsOracle ops rows =
    ops.foldl (fun acc op => applyQueryOpSubset op acc) rows := by
  induction ops generalizing rows with
  | nil =>
      simp [evalQueryOpsOracle]
  | cons op ops ih =>
      simp [evalQueryOpsOracle, ih]

theorem oracleQueryEvalSubset_eq_relational
  (q : Query)
  (snaps : SnapSet)
  (_hsupported : supportsQuerySubset q = true) :
  oracleQueryEvalSubset q snaps = evalQuerySubset q snaps := by
  unfold oracleQueryEvalSubset evalQuerySubset
  simpa using evalQueryOpsOracle_eq_foldl q.pipeline (evalSourceSubset q.source snaps)

end Cicsc.Core
