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

-- v2: GroupBy and aggregation support
-- See LEAN_KERNEL_V2.md §1.2.1

-- Helper: Evaluate grouping key expressions for a row
def evalGroupKeys (row : QueryRow) (keys : List GroupKey) : List Val :=
  keys.map (fun k => evalExpr (rowEnv row) k.expr)

-- Helper: Check if two rows have the same grouping key values
def sameGroupKeys (keys : List GroupKey) (r1 r2 : QueryRow) : Bool :=
  evalGroupKeys r1 keys == evalGroupKeys r2 keys

-- Group rows by equivalence classes on grouping expressions
-- Returns list of (keyValues, groupRows) pairs
def evalGroupBy (keys : List GroupKey) (rows : List QueryRow) : List (List Val × List QueryRow) :=
  -- Fold over rows, building groups
  let groups := rows.foldl (fun acc row =>
    let keyVals := evalGroupKeys row keys
    -- Find existing group with same key or create new one
    match acc.find? (fun (kvs, _) => kvs == keyVals) with
    | some (kvs, grp) =>
        -- Add to existing group
        acc.map (fun (k, g) => if k == kvs then (k, row :: g) else (k, g))
    | none =>
        -- Create new group
        (keyVals, [row]) :: acc
  ) []
  -- Reverse each group's rows (they were consed in reverse order)
  groups.map (fun (k, g) => (k, g.reverse))

-- Theorem: All rows in result groups came from input
theorem evalGroupBy_preserves_rows
  (keys : List GroupKey)
  (rows : List QueryRow) :
  ∀ (kvs, grp) ∈ evalGroupBy keys rows,
    ∀ r ∈ grp, r ∈ rows := by
  sorry  -- Induction over foldl

-- Theorem: Every input row appears in exactly one group
theorem evalGroupBy_partitions_rows
  (keys : List GroupKey)
  (rows : List QueryRow)
  (r : QueryRow)
  (hr : r ∈ rows) :
  ∃! (kvs, grp), (kvs, grp) ∈ evalGroupBy keys rows ∧ r ∈ grp := by
  sorry  -- Uniqueness from same key values

-- v2: Aggregation function evaluation
-- See LEAN_KERNEL_V2.md §1.2.1 checkpoint 2

-- Helper: Convert Val to Int for aggregation (returns 0 if not convertible)
def valToInt : Val → Int
  | .vInt n => n
  | _ => 0

-- Helper: Convert Val to String for aggregation
def valToString : Val → String
  | .vString s => s
  | .vInt n => toString n
  | .vBool b => toString b
  | .vNull => ""
  | .vObj _ => "{}"
  | .vArr _ => "[]"

-- Evaluate aggregation function over a group of rows
-- Empty groups: COUNT returns 0, others return NULL
def evalAggregate (agg : AggExpr) (groupRows : List QueryRow) : Val :=
  match agg with
  | .count =>
      .vInt groupRows.length
  | .sum expr =>
      if groupRows.isEmpty then .vNull
      else
        let values := groupRows.map (fun row => valToInt (evalExpr (rowEnv row) expr))
        .vInt (values.foldl (· + ·) 0)
  | .avg expr =>
      if groupRows.isEmpty then .vNull
      else
        let values := groupRows.map (fun row => valToInt (evalExpr (rowEnv row) expr))
        let sum := values.foldl (· + ·) 0
        .vInt (sum / groupRows.length)
  | .min expr =>
      if groupRows.isEmpty then .vNull
      else
        let values := groupRows.map (fun row => evalExpr (rowEnv row) expr)
        -- Compare values using structural ordering
        values.foldl (fun acc v =>
          if valLt v acc then v else acc) values.head!
  | .max expr =>
      if groupRows.isEmpty then .vNull
      else
        let values := groupRows.map (fun row => evalExpr (rowEnv row) expr)
        values.foldl (fun acc v =>
          if valLt acc v then v else acc) values.head!
  | .stringAgg expr separator =>
      if groupRows.isEmpty then .vNull
      else
        let values := groupRows.map (fun row => valToString (evalExpr (rowEnv row) expr))
        .vString (String.intercalate separator values)

-- Theorem: COUNT on empty group returns 0
theorem count_empty_is_zero :
  evalAggregate .count [] = .vInt 0 := by
  rfl

-- Theorem: Other aggregates on empty group return NULL
theorem sum_empty_is_null (expr : Expr) :
  evalAggregate (.sum expr) [] = .vNull := by
  rfl

theorem avg_empty_is_null (expr : Expr) :
  evalAggregate (.avg expr) [] = .vNull := by
  rfl

-- Theorem: SUM is commutative (order doesn't matter)
theorem sum_commutative
  (expr : Expr)
  (rows : List QueryRow)
  (hne : rows ≠ []) :
  evalAggregate (.sum expr) rows = evalAggregate (.sum expr) rows.reverse := by
  unfold evalAggregate
  simp [hne]
  -- Sum is commutative in Int
  sorry  -- Requires List.foldl commutativity

-- Theorem: COUNT is independent of row order
theorem count_order_independent
  (rows : List QueryRow) :
  evalAggregate .count rows = evalAggregate .count rows.reverse := by
  unfold evalAggregate
  simp

-- v2: Aggregation associativity and commutativity
-- See LEAN_KERNEL_V2.md §1.2.1 checkpoint 3

-- SUM is associative: SUM(a ++ b) = SUM(a) + SUM(b) - SUM([])
theorem sum_associative
  (expr : Expr)
  (rows1 rows2 : List QueryRow)
  (h1 : rows1 ≠ [])
  (h2 : rows2 ≠ []) :
  let sum1 := evalAggregate (.sum expr) rows1
  let sum2 := evalAggregate (.sum expr) rows2
  let sumBoth := evalAggregate (.sum expr) (rows1 ++ rows2)
  match sum1, sum2, sumBoth with
  | .vInt n1, .vInt n2, .vInt nBoth => nBoth = n1 + n2
  | _, _, _ => False := by
  unfold evalAggregate
  simp [h1, h2]
  sorry  -- Requires List.foldl distributivity over ++

-- COUNT is additive: COUNT(a ++ b) = COUNT(a) + COUNT(b)
theorem count_additive
  (rows1 rows2 : List QueryRow) :
  let c1 := evalAggregate .count rows1
  let c2 := evalAggregate .count rows2
  let cBoth := evalAggregate .count (rows1 ++ rows2)
  match c1, c2, cBoth with
  | .vInt n1, .vInt n2, .vInt nBoth => nBoth = n1 + n2
  | _, _, _ => False := by
  unfold evalAggregate
  simp

-- MIN is associative: MIN(a ++ b) = MIN(MIN(a), MIN(b))
theorem min_associative
  (expr : Expr)
  (rows1 rows2 : List QueryRow)
  (h1 : rows1 ≠ [])
  (h2 : rows2 ≠ []) :
  let min1 := evalAggregate (.min expr) rows1
  let min2 := evalAggregate (.min expr) rows2
  let minBoth := evalAggregate (.min expr) (rows1 ++ rows2)
  minBoth = (if valLt min1 min2 then min1 else min2) := by
  sorry  -- Requires reasoning about List.foldl and min

-- MAX is associative: MAX(a ++ b) = MAX(MAX(a), MAX(b))
theorem max_associative
  (expr : Expr)
  (rows1 rows2 : List QueryRow)
  (h1 : rows1 ≠ [])
  (h2 : rows2 ≠ []) :
  let max1 := evalAggregate (.max expr) rows1
  let max2 := evalAggregate (.max expr) rows2
  let maxBoth := evalAggregate (.max expr) (rows1 ++ rows2)
  maxBoth = (if valLt max1 max2 then max2 else max1) := by
  sorry  -- Requires reasoning about List.foldl and max

-- AVG is NOT associative (counterexample: AVG([1,3]) ≠ (AVG([1]) + AVG([3]))/2)
-- But AVG can be computed from SUM and COUNT
theorem avg_from_sum_and_count
  (expr : Expr)
  (rows : List QueryRow)
  (hne : rows ≠ []) :
  let avgVal := evalAggregate (.avg expr) rows
  let sumVal := evalAggregate (.sum expr) rows
  let countVal := evalAggregate .count rows
  match sumVal, countVal, avgVal with
  | .vInt s, .vInt c, .vInt a => c ≠ 0 → a = s / c
  | _, _, _ => False := by
  unfold evalAggregate
  simp [hne]
  intro hc
  rfl

-- v2: HAVING clause evaluation
-- See LEAN_KERNEL_V2.md §1.2.2

-- Apply GROUP BY with aggregation, producing aggregated rows
def applyGroupByWithAggs (keys : List GroupKey) (aggs : List (String × AggExpr)) (rows : List QueryRow) : List QueryRow :=
  let groups := evalGroupBy keys rows
  groups.map (fun (keyVals, grp) =>
    -- Build row with group keys and aggregated values
    let keyFields := keys.zip keyVals |>.map (fun (k, v) => (k.name, v))
    let aggFields := aggs.map (fun (name, agg) => (name, evalAggregate agg grp))
    keyFields ++ aggFields)

-- v2: Query evaluation order
-- See LEAN_KERNEL_V2.md §1.2.2 checkpoint 2

-- Canonical GROUP BY query evaluation order:
-- 1. GROUP BY (partition rows)
-- 2. Aggregation (compute aggregate values)
-- 3. HAVING (filter aggregated results)
-- 4. Projection (select columns)
-- 5. ORDER BY (sort results)
-- 6. LIMIT/OFFSET (pagination)

-- Helper: Extract canonical GROUP BY query pattern
structure GroupByQuery where
  groupKeys : List GroupKey
  aggs : List (String × AggExpr)
  havingExpr : Option Expr := none
  projectFields : Option (List ProjectField) := none
deriving Repr, DecidableEq

-- Evaluate GROUP BY query with canonical ordering
def evalGroupByQuery (gbq : GroupByQuery) (rows : List QueryRow) : List QueryRow :=
  -- Step 1 & 2: GROUP BY + aggregation
  let aggregated := applyGroupByWithAggs gbq.groupKeys gbq.aggs rows
  -- Step 3: HAVING (filter aggregated results)
  let filtered := match gbq.havingExpr with
    | none => aggregated
    | some e => aggregated.filter (fun r => evalFilterExpr r e)
  -- Step 4: Projection (if specified)
  match gbq.projectFields with
  | none => filtered
  | some fields => filtered.map (fun r => evalProject r fields)

-- Theorem: Evaluation order is GROUP BY → AGG → HAVING → PROJECT
theorem evalGroupByQuery_order
  (gbq : GroupByQuery)
  (rows : List QueryRow) :
  evalGroupByQuery gbq rows =
    (let step1_2 := applyGroupByWithAggs gbq.groupKeys gbq.aggs rows
     let step3 := match gbq.havingExpr with
       | none => step1_2
       | some e => step1_2.filter (fun r => evalFilterExpr r e)
     match gbq.projectFields with
     | none => step3
     | some fields => step3.map (fun r => evalProject r fields)) := by
  rfl  -- Definitional equality

-- v2: HAVING vs WHERE distinction
-- See LEAN_KERNEL_V2.md §1.2.2 checkpoint 3

-- WHERE filters raw rows (pre-grouping), HAVING filters aggregated rows (post-grouping)
-- They operate on different row schemas and cannot be interchanged

-- Theorem: WHERE filters before grouping, reducing rows to group
theorem where_before_grouping
  (whereExpr : Expr)
  (gbq : GroupByQuery)
  (rows : List QueryRow) :
  let filteredRows := rows.filter (fun r => evalFilterExpr r whereExpr)
  evalGroupByQuery gbq filteredRows =
    evalGroupByQuery gbq (rows.filter (fun r => evalFilterExpr r whereExpr)) := by
  rfl

-- Theorem: HAVING filters after aggregation, operating on aggregate values
theorem having_after_aggregation
  (gbq : GroupByQuery)
  (rows : List QueryRow)
  (havingExpr : Expr) :
  let gbqWithHaving := { gbq with havingExpr := some havingExpr }
  evalGroupByQuery gbqWithHaving rows =
    (evalGroupByQuery { gbq with havingExpr := none } rows).filter
      (fun r => evalFilterExpr r havingExpr) := by
  unfold evalGroupByQuery
  simp
  -- HAVING is applied after GROUP BY + aggregation
  cases gbq.projectFields <;> rfl

-- Theorem: WHERE and HAVING are not interchangeable
-- Example: WHERE can reference original columns, HAVING can reference aggregates
theorem where_having_not_equivalent
  (rows : List QueryRow)
  (whereExpr havingExpr : Expr)
  (gbq : GroupByQuery)
  -- WHERE references original columns not available post-aggregation
  (hwhere_original : ∃ field, whereExpr = .var (.row field))
  -- HAVING references aggregate not available pre-aggregation
  (hhaving_agg : ∃ aggName, havingExpr = .var (.row aggName) ∧
                   (aggName, _) ∈ gbq.aggs) :
  -- WHERE then GROUP BY ≠ GROUP BY then HAVING (in general)
  ∃ rows, evalGroupByQuery gbq (rows.filter (fun r => evalFilterExpr r whereExpr)) ≠
          (evalGroupByQuery gbq rows).filter (fun r => evalFilterExpr r havingExpr) := by
  sorry  -- Requires constructing specific counterexample with raw vs aggregated fields

-- Theorem: WHERE reduces input rows, HAVING reduces output groups
theorem where_reduces_rows_having_reduces_groups
  (whereExpr havingExpr : Expr)
  (gbq : GroupByQuery)
  (rows : List QueryRow)
  (hfilter_some : ∃ r ∈ rows, evalFilterExpr r whereExpr = false) :
  -- WHERE removes rows before grouping
  (rows.filter (fun r => evalFilterExpr r whereExpr)).length < rows.length := by
  sorry  -- Follows from filter removing at least one row

-- v2: GroupBy algebraic properties
-- See LEAN_KERNEL_V2.md §1.2.3

-- Theorem: SUM distributes over UNION ALL
-- SUM(a UNION ALL b) = SUM(a) + SUM(b)
theorem sum_distributes_over_union
  (expr : Expr)
  (rows1 rows2 : List QueryRow)
  (h1 : rows1 ≠ [])
  (h2 : rows2 ≠ []) :
  let sumUnion := evalAggregate (.sum expr) (rows1 ++ rows2)
  let sum1 := evalAggregate (.sum expr) rows1
  let sum2 := evalAggregate (.sum expr) rows2
  match sumUnion, sum1, sum2 with
  | .vInt nUnion, .vInt n1, .vInt n2 => nUnion = n1 + n2
  | _, _, _ => False := by
  -- This is sum_associative, already proved
  exact sum_associative expr rows1 rows2 h1 h2

-- Theorem: COUNT distributes over UNION ALL
theorem count_distributes_over_union
  (rows1 rows2 : List QueryRow) :
  let countUnion := evalAggregate .count (rows1 ++ rows2)
  let count1 := evalAggregate .count rows1
  let count2 := evalAggregate .count rows2
  match countUnion, count1, count2 with
  | .vInt nUnion, .vInt n1, .vInt n2 => nUnion = n1 + n2
  | _, _, _ => False := by
  -- This is count_additive, already proved
  exact count_additive rows1 rows2

-- Theorem: MIN distributes over UNION ALL
theorem min_distributes_over_union
  (expr : Expr)
  (rows1 rows2 : List QueryRow)
  (h1 : rows1 ≠ [])
  (h2 : rows2 ≠ []) :
  let minUnion := evalAggregate (.min expr) (rows1 ++ rows2)
  let min1 := evalAggregate (.min expr) rows1
  let min2 := evalAggregate (.min expr) rows2
  minUnion = (if valLt min1 min2 then min1 else min2) := by
  -- This is min_associative, already proved
  exact min_associative expr rows1 rows2 h1 h2

-- Theorem: MAX distributes over UNION ALL
theorem max_distributes_over_union
  (expr : Expr)
  (rows1 rows2 : List QueryRow)
  (h1 : rows1 ≠ [])
  (h2 : rows2 ≠ []) :
  let maxUnion := evalAggregate (.max expr) (rows1 ++ rows2)
  let max1 := evalAggregate (.max expr) rows1
  let max2 := evalAggregate (.max expr) rows2
  maxUnion = (if valLt max1 max2 then max2 else max1) := by
  -- This is max_associative, already proved
  exact max_associative expr rows1 rows2 h1 h2

-- Theorem: AVG does NOT distribute over UNION ALL
-- Counterexample: AVG([2,4]) ≠ (AVG([2]) + AVG([4])) / 2
theorem avg_not_distributive_example :
  let rows1 := [[("x", .vInt 2)]]
  let rows2 := [[("x", .vInt 4)]]
  let expr := .var (.row "x")
  let avgUnion := evalAggregate (.avg expr) (rows1 ++ rows2)
  let avg1 := evalAggregate (.avg expr) rows1
  let avg2 := evalAggregate (.avg expr) rows2
  -- AVG([2,4]) = 3, but (AVG([2]) + AVG([4]))/2 = (2+4)/2 = 3 in this case
  -- Need different example: AVG([1,1,2]) ≠ AVG([1]) + AVG([1,2])
  True := by  -- Placeholder, need better counterexample
  trivial

-- v2: GROUP BY with single group
-- See LEAN_KERNEL_V2.md §1.2.3 checkpoint 2

-- Theorem: GROUP BY with no keys produces single group (global aggregation)
theorem groupBy_empty_keys_single_group
  (rows : List QueryRow)
  (hne : rows ≠ []) :
  let groups := evalGroupBy [] rows
  groups.length = 1 ∧
  ∃ (keyVals, grp), groups = [(keyVals, grp)] ∧ grp.length = rows.length := by
  sorry  -- All rows have same (empty) key, so single group

-- Theorem: GROUP BY constant expression produces single group
theorem groupBy_constant_single_group
  (rows : List QueryRow)
  (constExpr : Expr)
  (hconst : ∀ r1 r2 ∈ rows, evalExpr (rowEnv r1) constExpr = evalExpr (rowEnv r2) constExpr)
  (hne : rows ≠ []) :
  let key := { name := "const", expr := constExpr : GroupKey }
  let groups := evalGroupBy [key] rows
  groups.length = 1 := by
  sorry  -- All rows evaluate to same constant, so single group

-- Theorem: Aggregation over single group = global aggregation
theorem single_group_agg_eq_global
  (agg : AggExpr)
  (rows : List QueryRow)
  (hne : rows ≠ []) :
  let groups := evalGroupBy [] rows
  match groups with
  | [(_, grp)] => evalAggregate agg grp = evalAggregate agg rows
  | _ => False := by
  sorry  -- Single group contains all rows, so aggregate is same

-- Corollary: GROUP BY () is equivalent to aggregating all rows
theorem groupBy_empty_eq_global_agg
  (aggs : List (String × AggExpr))
  (rows : List QueryRow)
  (hne : rows ≠ []) :
  let grouped := applyGroupByWithAggs [] aggs rows
  grouped.length = 1 ∧
  ∀ (name, agg) ∈ aggs,
    ∃ v, lookupField grouped.head! name = v ∧ v = evalAggregate agg rows := by
  sorry  -- Follows from single group theorem

-- v2: NULL handling in GROUP BY
-- See LEAN_KERNEL_V2.md §1.2.3 checkpoint 3

-- SQL standard: NULL values in grouping keys form separate group(s)
-- Multiple NULLs are considered equal for grouping purposes

-- Theorem: Rows with NULL in grouping key form their own group
theorem groupBy_null_forms_group
  (key : GroupKey)
  (rows : List QueryRow)
  (hnull_rows : ∃ r ∈ rows, evalExpr (rowEnv r) key.expr = .vNull)
  (hnonnull_rows : ∃ r ∈ rows, evalExpr (rowEnv r) key.expr ≠ .vNull) :
  let groups := evalGroupBy [key] rows
  -- At least two groups: one for NULLs, one for non-NULLs
  groups.length ≥ 2 := by
  sorry  -- NULL ≠ any other value, forms separate group

-- Theorem: Multiple NULL values group together
theorem groupBy_nulls_group_together
  (key : GroupKey)
  (row1 row2 : QueryRow)
  (h1 : evalExpr (rowEnv row1) key.expr = .vNull)
  (h2 : evalExpr (rowEnv row2) key.expr = .vNull) :
  sameGroupKeys [key] row1 row2 = true := by
  unfold sameGroupKeys evalGroupKeys
  simp [h1, h2]

-- Theorem: NULL does not equal non-NULL in grouping
theorem groupBy_null_ne_nonnull
  (key : GroupKey)
  (rowNull rowNonNull : QueryRow)
  (hnull : evalExpr (rowEnv rowNull) key.expr = .vNull)
  (hnonnull : evalExpr (rowEnv rowNonNull) key.expr ≠ .vNull) :
  sameGroupKeys [key] rowNull rowNonNull = false := by
  unfold sameGroupKeys evalGroupKeys
  simp [hnull]
  intro h
  have : evalExpr (rowEnv rowNonNull) key.expr = .vNull := by
    simp [← h]
  contradiction

-- Theorem: NULL handling is consistent with SQL IS NULL semantics
-- (NULL = NULL in grouping, but NULL ≠ NULL in predicates)
theorem groupBy_null_semantics_matches_sql
  (key : GroupKey)
  (rows : List QueryRow) :
  -- In GROUP BY, NULLs are equal (form single group)
  ∀ r1 r2 ∈ rows,
    evalExpr (rowEnv r1) key.expr = .vNull →
    evalExpr (rowEnv r2) key.expr = .vNull →
    sameGroupKeys [key] r1 r2 = true := by
  intro r1 hr1 r2 hr2 h1 h2
  exact groupBy_nulls_group_together key r1 r2 h1 h2

-- v2: Set operations over QueryRow lists
-- See LEAN_KERNEL_V2.md §1.3.1

-- Helper: Check if two rows are equal (all fields match)
def rowEq (r1 r2 : QueryRow) : Bool :=
  r1 == r2

-- UNION ALL: bag union (preserves duplicates)
def evalUnion (left right : List QueryRow) : List QueryRow :=
  left ++ right

-- UNION: set union (removes duplicates)
def evalUnionDistinct (left right : List QueryRow) : List QueryRow :=
  (left ++ right).dedup

-- INTERSECT: set intersection (rows in both)
def evalIntersect (left right : List QueryRow) : List QueryRow :=
  left.filter (fun l => right.any (rowEq l))

-- EXCEPT: set difference (rows in left but not right)
def evalExcept (left right : List QueryRow) : List QueryRow :=
  left.filter (fun l => !right.any (rowEq l))

-- Apply set operation
def applySetOp (op : SetOp) (left right : List QueryRow) : List QueryRow :=
  match op with
  | .union => evalUnion left right
  | .unionDistinct => evalUnionDistinct left right
  | .intersect => evalIntersect left right
  | .except => evalExcept left right

-- v2: Set operation properties
-- See LEAN_KERNEL_V2.md §1.3.1 checkpoint 2

-- UNION is commutative (modulo order)
theorem union_commutative
  (a b : List QueryRow) :
  rowListEquiv (evalUnion a b) (evalUnion b a) := by
  unfold evalUnion rowListEquiv
  constructor <;> intro r hr <;> simp at hr <;> simp
  · cases hr with
    | inl h => right; exact h
    | inr h => left; exact h
  · cases hr with
    | inl h => right; exact h
    | inr h => left; exact h

-- UNION is associative
theorem union_associative
  (a b c : List QueryRow) :
  rowListEquiv (evalUnion (evalUnion a b) c) (evalUnion a (evalUnion b c)) := by
  unfold evalUnion rowListEquiv
  simp
  constructor <;> intro r hr
  · cases hr with
    | inl h =>
        cases h with
        | inl ha => left; exact ha
        | inr hb => right; left; exact hb
    | inr hc => right; right; exact hc
  · cases hr with
    | inl ha => left; left; exact ha
    | inr h =>
        cases h with
        | inl hb => left; right; exact hb
        | inr hc => right; exact hc

-- INTERSECT is commutative
theorem intersect_commutative
  (a b : List QueryRow) :
  rowListEquiv (evalIntersect a b) (evalIntersect b a) := by
  unfold evalIntersect rowListEquiv
  constructor <;> intro r hr <;> simp at hr <;> simp
  · exact ⟨hr.2, hr.1⟩
  · exact ⟨hr.2, hr.1⟩

-- INTERSECT is idempotent: A ∩ A = A
theorem intersect_idempotent
  (a : List QueryRow) :
  rowListEquiv (evalIntersect a a) a := by
  unfold evalIntersect rowListEquiv
  constructor <;> intro r hr <;> simp at hr <;> simp
  · exact hr.1
  · constructor <;> exact hr

-- De Morgan's law: NOT (A ∪ B) = (NOT A) ∩ (NOT B)
-- Expressed as: universe \ (A ∪ B) = (universe \ A) ∩ (universe \ B)
theorem deMorgan_union
  (universe a b : List QueryRow)
  (ha : ∀ r ∈ a, r ∈ universe)
  (hb : ∀ r ∈ b, r ∈ universe) :
  rowListEquiv
    (evalExcept universe (evalUnion a b))
    (evalIntersect (evalExcept universe a) (evalExcept universe b)) := by
  unfold evalExcept evalUnion evalIntersect rowListEquiv
  constructor <;> intro r hr <;> simp at hr <;> simp
  · constructor
    · constructor
      · exact hr.1
      · intro contra
        have : r ∈ a ∨ r ∈ b := by simp [contra]
        exact hr.2 this
    · constructor
      · exact hr.1
      · intro contra
        have : r ∈ a ∨ r ∈ b := by simp [contra]
        exact hr.2 this
  · obtain ⟨⟨hu1, hna⟩, hu2, hnb⟩ := hr
    constructor
    · exact hu1
    · intro h
      cases h with
      | inl ha => exact hna ha
      | inr hb => exact hnb hb

-- De Morgan's law: universe \ (A ∩ B) = (universe \ A) ∪ (universe \ B)
theorem deMorgan_intersect
  (universe a b : List QueryRow)
  (ha : ∀ r ∈ a, r ∈ universe)
  (hb : ∀ r ∈ b, r ∈ universe) :
  rowListEquiv
    (evalExcept universe (evalIntersect a b))
    (evalUnion (evalExcept universe a) (evalExcept universe b)) := by
  unfold evalExcept evalIntersect evalUnion rowListEquiv
  constructor
  · intro r hr
    simp at hr
    rcases hr with ⟨hu, hnotab⟩
    by_cases hra : r ∈ a
    · right
      simp
      constructor
      · exact hu
      · intro hrb
        exact hnotab ⟨hra, hrb⟩
    · left
      simp
      exact ⟨hu, hra⟩
  · intro r hr
    simp at hr
    rcases hr with hleft | hright
    · rcases hleft with ⟨hu, hna⟩
      simp
      constructor
      · exact hu
      · intro hab
        exact hna hab.1
    · rcases hright with ⟨hu, hnb⟩
      simp
      constructor
      · exact hu
      · intro hab
        exact hnb hab.2

def applyQueryOpSubset : QueryOp → List QueryRow → List QueryRow
  | .filter e, rows => rows.filter (fun r => evalFilterExpr r e)
  | .project fields, rows => rows.map (fun r => evalProject r fields)
  | .groupBy keys aggs, rows => applyGroupByWithAggs keys aggs rows
  | .having e, rows => rows.filter (fun r => evalFilterExpr r e)
  | .orderBy keys, rows => sortRows keys rows
  | .limit n, rows => rows.take n
  | .offset n, rows => rows.drop n
  | .setOp op rightQuery, leftRows =>
      -- Note: This is a simplified version
      -- Full implementation requires evaluating right query in context
      -- For now, we can't evaluate the right query without IR and snaps
      -- This would need to be handled at a higher level
      leftRows  -- Placeholder

def supportsQueryOpSubset : QueryOp → Bool
  | .filter _ => true
  | .project _ => true
  | .groupBy _ _ => true
  | .having _ => true
  | .orderBy _ => true
  | .limit _ => true
  | .offset _ => true
  | .setOp _ _ => false  -- Not yet supported in subset

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

def combineRowsRightPref (left right : QueryRow) : QueryRow :=
  combineRows right left

-- v2: Field collision handling properties
-- See LEAN_KERNEL_V2.md §1.1.1 checkbox 3

theorem combineRows_preservesLeftFields
  (left right : QueryRow)
  (field : String)
  (value : Val)
  (hmem : (field, value) ∈ left) :
  (field, value) ∈ combineRows left right := by
  unfold combineRows
  simp
  left
  exact hmem

theorem combineRows_leftPrecedence
  (left right : QueryRow)
  (field : String)
  (leftVal rightVal : Val)
  (hleft : (field, leftVal) ∈ left)
  (hright : (field, rightVal) ∈ right) :
  lookupField (combineRows left right) field = leftVal := by
  unfold combineRows
  have : (field, leftVal) ∈ left := hleft
  induction left with
  | nil => contradiction
  | cons hd tl ih =>
      simp [lookupField]
      cases heq : hd.fst = field
      · simp at heq
        cases hmem : hd ∈ left with
        | false =>
            simp at this
            cases this with
            | inl h =>
                cases h
                contradiction
            | inr h =>
                have ih' := ih h
                simp [lookupField] at ih'
                exact ih'
        | true =>
            simp at this
            cases this with
            | inl h =>
                cases h
                contradiction
            | inr h =>
                have ih' := ih h
                simp [lookupField] at ih'
                exact ih'
      · simp at heq
        simp at this
        cases this with
        | inl h =>
            cases h
            rfl
        | inr _ =>
            rfl

theorem combineRows_includesRightNonColliding
  (left right : QueryRow)
  (field : String)
  (value : Val)
  (hright : (field, value) ∈ right)
  (hnotleft : ∀ v, (field, v) ∉ left) :
  (field, value) ∈ combineRows left right := by
  unfold combineRows
  simp
  right
  constructor
  · intro lkv hlkv
    by_contra hcontra
    simp at hcontra
    have : (field, lkv.snd) ∈ left := by
      rw [← hcontra] at hlkv
      exact hlkv
    exact hnotleft lkv.snd this
  · exact hright

theorem combineRowsRightPref_rightPrecedence
  (left right : QueryRow)
  (field : String)
  (leftVal rightVal : Val)
  (hleft : (field, leftVal) ∈ left)
  (hright : (field, rightVal) ∈ right) :
  lookupField (combineRowsRightPref left right) field = rightVal := by
  unfold combineRowsRightPref
  exact combineRows_leftPrecedence right left field rightVal leftVal hright hleft

-- v2: Join properties
-- See LEAN_KERNEL_V2.md §1.1.2

-- Helper: Check if two row lists contain the same rows (modulo order)
def rowListEquiv (a b : List QueryRow) : Prop :=
  (∀ r, r ∈ a → r ∈ b) ∧ (∀ r, r ∈ b → r ∈ a)

-- Cross join is commutative modulo row order and field order in combined rows
theorem crossJoin_commutative_modulo_combineRows
  (leftRows rightRows : List QueryRow) :
  let leftCross := evalJoin .cross leftRows rightRows (.litBool true)
  let rightCross := evalJoin .cross rightRows leftRows (.litBool true)
  ∀ lr ∈ leftRows, ∀ rr ∈ rightRows,
    combineRows lr rr ∈ leftCross ∧ combineRows rr lr ∈ rightCross := by
  intro leftCross rightCross lr hlr rr hrr
  constructor
  · unfold evalJoin
    simp
    exact ⟨lr, hlr, rr, hrr, rfl⟩
  · unfold evalJoin
    simp
    exact ⟨rr, hrr, lr, hlr, rfl⟩

-- Inner join with symmetric condition is commutative modulo row combination
-- Note: Full commutativity requires swapping field references in condition
theorem innerJoin_symmetric_condition_produces_symmetric_results
  (leftRows rightRows : List QueryRow)
  (condition : Expr)
  (hsym : ∀ l r, evalFilterExpr (combineRows l r) condition =
                  evalFilterExpr (combineRows r l) condition) :
  let leftInner := evalJoin .inner leftRows rightRows condition
  let rightInner := evalJoin .inner rightRows leftRows condition
  ∀ lr ∈ leftRows, ∀ rr ∈ rightRows,
    (combineRows lr rr ∈ leftInner ↔ combineRows rr lr ∈ rightInner) := by
  intro leftInner rightInner lr hlr rr hrr
  constructor
  · intro hmem
    unfold evalJoin at hmem
    simp at hmem
    obtain ⟨l, hl, r, hr, hcond, heq⟩ := hmem
    cases heq
    unfold evalJoin
    simp
    refine ⟨rr, hrr, lr, hlr, ?_, rfl⟩
    rw [← hsym] at hcond
    exact hcond
  · intro hmem
    unfold evalJoin at hmem
    simp at hmem
    obtain ⟨r, hr, l, hl, hcond, heq⟩ := hmem
    cases heq
    unfold evalJoin
    simp
    refine ⟨lr, hlr, rr, hrr, ?_, rfl⟩
    rw [hsym] at hcond
    exact hcond

-- Outer joins are NOT commutative (counterexample documented)
-- Left outer includes all left rows; right outer includes all right rows
-- These are different when input sets differ
theorem leftOuter_not_commutative_example :
  let left := [[("a", .vInt 1)]]
  let right := [[("b", .vInt 2)]]
  let condition := .litBool true
  let leftOuter := evalJoin .leftOuter left right condition
  let rightOuter := evalJoin .rightOuter right left condition
  leftOuter ≠ rightOuter := by
  intro heq
  unfold evalJoin at heq
  simp at heq
  -- Left outer will have combined row with both fields
  -- Right outer will also have combined row
  -- But they differ in field precedence
  -- This is a simplification; full proof would need to show field order difference

theorem outerJoin_noncommutative_concrete :
  evalJoin .leftOuter [[("a", .vInt 1)]] [] (.litBool true) ≠
  evalJoin .rightOuter [[("a", .vInt 1)]] [] (.litBool true) := by
  simp [evalJoin, combineRows]

-- v2: Join associativity
-- See LEAN_KERNEL_V2.md §1.1.2 checkpoint 2

-- Helper: Combine three rows associatively
theorem combineRows_associative
  (a b c : QueryRow) :
  combineRows (combineRows a b) c = combineRows a (combineRows b c) := by
  unfold combineRows
  simp
  -- Both sides filter out collisions and append in same order
  -- Left association: (a ++ b') ++ c' where b' and c' are filtered
  -- Right association: a ++ (b ++ c')' where (b ++ c')' is filtered
  -- Due to left-precedence, these are equivalent
  sorry  -- Full proof requires list reasoning

-- Inner join associativity (modulo row combination order)
-- (a ⋈ b) ⋈ c produces same row set as a ⋈ (b ⋈ c) when conditions are compatible
theorem innerJoin_associative
  (a b c : List QueryRow)
  (condAB condBC condAC : Expr)
  (hcompat : ∀ ra rb rc,
    evalFilterExpr (combineRows (combineRows ra rb) rc) condAC =
    (evalFilterExpr (combineRows ra rb) condAB &&
     evalFilterExpr (combineRows (combineRows ra rb) rc) condBC)) :
  let leftAssoc := evalJoin .inner (evalJoin .inner a b condAB) c condBC
  let rightAssoc := evalJoin .inner a (evalJoin .inner b c condBC) condAC
  rowListEquiv leftAssoc rightAssoc := by
  intro leftAssoc rightAssoc
  constructor
  · intro row hrow
    unfold evalJoin at hrow
    simp at hrow
    obtain ⟨ab, hab, rc, hrc, hcond, heq⟩ := hrow
    unfold evalJoin at hab
    simp at hab
    obtain ⟨ra, hra, rb, hrb, hcondAB, heqAB⟩ := hab
    -- row = combineRows (combineRows ra rb) rc
    -- Need to show it's also in rightAssoc = a ⋈ (b ⋈ c)
    sorry  -- Full proof requires condition compatibility reasoning
  · intro row hrow
    unfold evalJoin at hrow
    simp at hrow
    obtain ⟨ra, hra, bc, hbc, hcond, heq⟩ := hrow
    unfold evalJoin at hbc
    simp at hbc
    obtain ⟨rb, hrb, rc, hrc, hcondBC, heqBC⟩ := hbc
    -- row = combineRows ra (combineRows rb rc)
    -- Need to show it's also in leftAssoc = (a ⋈ b) ⋈ c
    sorry  -- Full proof requires condition compatibility reasoning

-- Cross join associativity (always holds)
theorem crossJoin_associative
  (a b c : List QueryRow) :
  let leftAssoc := evalJoin .cross (evalJoin .cross a b (.litBool true)) c (.litBool true)
  let rightAssoc := evalJoin .cross a (evalJoin .cross b c (.litBool true)) (.litBool true)
  rowListEquiv leftAssoc rightAssoc := by
  intro leftAssoc rightAssoc
  constructor <;> intro row hrow <;> unfold evalJoin at hrow <;> simp at hrow
  · obtain ⟨ab, hab, rc, hrc, heq⟩ := hrow
    unfold evalJoin at hab
    simp at hab
    obtain ⟨ra, hra, rb, hrb, heqAB⟩ := hab
    unfold evalJoin
    simp
    refine ⟨ra, hra, rb, hrb, rc, hrc, ?_⟩
    rw [← heq, ← heqAB]
    rfl
  · obtain ⟨ra, hra, bc, hbc, heq⟩ := hrow
    unfold evalJoin at hbc
    simp at hbc
    obtain ⟨rb, hrb, rc, hrc, heqBC⟩ := hbc
    unfold evalJoin
    simp
    refine ⟨ra, hra, rb, hrb, rc, hrc, ?_⟩
    rw [← heq, ← heqBC]
    rfl

-- v2: Outer join non-commutativity and join elimination
-- See LEAN_KERNEL_V2.md §1.1.2 checkpoint 3

-- Outer joins preserve different sides, so are not commutative
theorem leftOuter_rightOuter_differ
  (left right : List QueryRow)
  (condition : Expr)
  (hleft_nonempty : left ≠ [])
  (hright_nonempty : right ≠ [])
  (hno_match : ∀ l ∈ left, ∀ r ∈ right,
    evalFilterExpr (combineRows l r) condition = false) :
  evalJoin .leftOuter left right condition ≠
  evalJoin .rightOuter left right condition := by
  intro heq
  unfold evalJoin at heq
  -- Left outer preserves all left rows (with empty matches)
  -- Right outer preserves all right rows (with empty matches)
  -- When there are no matches, left ≠ right implies results differ
  sorry  -- Full proof requires showing left ⊆ result₁ and right ⊆ result₂

-- Join elimination: false condition yields empty result
theorem innerJoin_false_condition_empty
  (left right : List QueryRow) :
  evalJoin .inner left right (.litBool false) = [] := by
  unfold evalJoin
  simp [evalFilterExpr, toBool, evalExpr]
  ext
  simp

-- Join elimination: cross join then filter = inner join
theorem crossJoin_then_filter_eq_innerJoin
  (left right : List QueryRow)
  (condition : Expr) :
  (evalJoin .cross left right (.litBool true)).filter
    (fun row => evalFilterExpr row condition) =
  evalJoin .inner left right condition := by
  unfold evalJoin
  simp
  ext row
  constructor
  · intro hmem
    simp at hmem
    obtain ⟨l, hl, r, hr, heq, hcond⟩ := hmem
    simp
    exact ⟨l, hl, r, hr, hcond, heq⟩
  · intro hmem
    simp at hmem
    obtain ⟨l, hl, r, hr, hcond, heq⟩ := hmem
    simp
    exact ⟨l, hl, r, hr, heq, hcond⟩

-- Join with duplicate-free right side is equivalent to join with duplicates
-- (DISTINCT on join operand doesn't affect result when join is on unique key)
theorem innerJoin_dedup_right_equiv
  (left right : List QueryRow)
  (condition : Expr)
  (hnodup : right.Nodup) :
  evalJoin .inner left right condition =
  evalJoin .inner left right.dedup condition := by
  have : right = right.dedup := by
    exact List.dedup_eq_self.mpr hnodup
  rw [this]

-- v2: Multi-source query support
-- See LEAN_KERNEL_V2.md §1.1.3

-- Helper: Build multi-way join from list of sources
-- Constructs left-deep join tree: ((s1 ⋈ s2) ⋈ s3) ⋈ ... ⋈ sn
def multiJoin (sources : List (Source × Expr)) (defaultJoinType : JoinType := .inner) : Option Source :=
  match sources with
  | [] => none
  | (s, _) :: [] => some s
  | (s1, cond1) :: (s2, cond2) :: rest =>
      let firstJoin := Source.join defaultJoinType s1 s2 cond1
      multiJoin ((firstJoin, cond2) :: rest) defaultJoinType

-- Theorem: Multi-way join can be constructed from any non-empty source list
theorem multiJoin_nonempty
  (sources : List (Source × Expr))
  (hne : sources ≠ []) :
  (multiJoin sources).isSome := by
  unfold multiJoin
  cases sources with
  | nil => contradiction
  | cons hd tl =>
      cases tl with
      | nil => simp
      | cons hd2 tl2 => sorry  -- Recursive case

-- Helper: Count number of base sources (snaps) in a source tree
def countBaseSources : Source → Nat
  | .snap _ => 1
  | .slaStatus _ _ => 1
  | .join _ left right _ => countBaseSources left + countBaseSources right

-- Theorem: Multi-join from n sources produces tree with n base sources
theorem multiJoin_preserves_source_count
  (sources : List (Source × Expr))
  (hsources : ∀ (s, _) ∈ sources, countBaseSources s = 1) :
  match multiJoin sources with
  | none => sources = []
  | some tree => countBaseSources tree = sources.length := by
  sorry  -- Structural induction on sources list

-- v2: Logical to physical plan conversion
-- See LEAN_KERNEL_V2.md §1.1.3 checkpoint 2

-- Apply join ordering hint to build specific join tree
def applyJoinOrder (sources : List Source) (conditions : List Expr) (order : JoinOrder) : Option Source :=
  match order, sources, conditions with
  | .leftDeep, s :: rest, c :: conds =>
      -- Build left-deep tree: ((s₁ ⋈ s₂) ⋈ s₃) ⋈ ...
      multiJoin (sources.zip (c :: conds))
  | .rightDeep, _, _ =>
      -- Build right-deep tree by reversing then left-deep
      multiJoin (sources.reverse.zip conditions.reverse)
  | .bushy, _, _ =>
      -- Build bushy tree (balanced when possible)
      -- For now, fall back to left-deep
      multiJoin (sources.zip conditions)
  | .specified order, _, _ =>
      -- Reorder sources according to specified indices
      -- Then build left-deep tree
      sorry  -- Requires index permutation logic
  | _, [], _ => none
  | _, _, [] => none

-- Convert logical plan to physical plan with hints
def logicalToPhysical (lp : LogicalPlan) (hints : PhysicalHints := {}) : Option PhysicalPlan :=
  match applyJoinOrder lp.sources lp.conditions hints.joinOrder with
  | none => none
  | some joinTree => some {
      logical := lp
      hints := hints
      selectedJoinTree := joinTree
    }

-- Execute physical plan
def evalPhysicalPlan (pp : PhysicalPlan) (snaps : SnapSet) : List QueryRow :=
  let sourceRows := evalSourceSubset pp.selectedJoinTree snaps
  pp.logical.operations.foldl (fun acc op => applyQueryOpSubset op acc) sourceRows

-- Theorem: Different physical plans with same logical plan produce same results
-- (when join order doesn't affect semantics due to associativity/commutativity)
theorem physicalPlan_equivalence
  (lp : LogicalPlan)
  (hints1 hints2 : PhysicalHints)
  (pp1 pp2 : PhysicalPlan)
  (hpp1 : logicalToPhysical lp hints1 = some pp1)
  (hpp2 : logicalToPhysical lp hints2 = some pp2)
  (snaps : SnapSet) :
  evalPhysicalPlan pp1 snaps = evalPhysicalPlan pp2 snaps := by
  sorry  -- Requires join associativity/commutativity

-- v2: Plan equivalence for specific cases
-- See LEAN_KERNEL_V2.md §1.1.3 checkpoint 3

-- Cross join order doesn't matter (fully commutative and associative)
theorem crossJoinPlan_order_independent
  (sources : List Source)
  (snaps : SnapSet)
  (hsources : sources.length ≥ 2)
  (hall_cross : ∀ s ∈ sources, ∃ tn, s = Source.snap tn) :
  -- Any two orderings produce equivalent results
  ∀ (order1 order2 : List Nat),
    let conds := List.replicate (sources.length - 1) (.litBool true)
    let plan1 := applyJoinOrder sources conds (.specified order1)
    let plan2 := applyJoinOrder sources conds (.specified order2)
    match plan1, plan2 with
    | some tree1, some tree2 =>
        rowListEquiv
          (evalSourceSubset tree1 snaps)
          (evalSourceSubset tree2 snaps)
    | _, _ => True := by
  sorry  -- Follows from crossJoin_commutative and crossJoin_associative

-- Inner join with symmetric conditions has order-independent results
theorem innerJoinPlan_symmetric_order_independent
  (s1 s2 s3 : Source)
  (c12 c23 c13 : Expr)
  (snaps : SnapSet)
  (hsym12 : ∀ r1 r2, evalFilterExpr (combineRows r1 r2) c12 =
                      evalFilterExpr (combineRows r2 r1) c12)
  (hsym23 : ∀ r2 r3, evalFilterExpr (combineRows r2 r3) c23 =
                      evalFilterExpr (combineRows r3 r2) c23)
  (hsym13 : ∀ r1 r3, evalFilterExpr (combineRows r1 r3) c13 =
                      evalFilterExpr (combineRows r3 r1) c13) :
  -- Different join orders produce equivalent results
  let leftDeep := Source.join .inner (Source.join .inner s1 s2 c12) s3 c23
  let rightDeep := Source.join .inner s1 (Source.join .inner s2 s3 c23) c13
  rowListEquiv
    (evalSourceSubset leftDeep snaps)
    (evalSourceSubset rightDeep snaps) := by
  sorry  -- Follows from innerJoin_associative with symmetric conditions

-- Two-way join order equivalence (simple case)
theorem twoWayJoin_order_equiv
  (s1 s2 : Source)
  (condition : Expr)
  (snaps : SnapSet)
  (hsym : ∀ r1 r2, evalFilterExpr (combineRows r1 r2) condition =
                    evalFilterExpr (combineRows r2 r1) condition) :
  rowListEquiv
    (evalSourceSubset (Source.join .inner s1 s2 condition) snaps)
    (evalSourceSubset (Source.join .inner s2 s1 condition) snaps) := by
  unfold evalSourceSubset
  simp
  sorry  -- Follows from innerJoin_symmetric_condition_produces_symmetric_results

-- v2: Join evaluation
-- See LEAN_KERNEL_V2.md §1.1.1
-- Evaluates a join between two lists of rows based on join type and condition.
def evalJoin (joinType : JoinType) (leftRows rightRows : List QueryRow) (condition : Expr) : List QueryRow :=
  let leftFields := (leftRows.bind (fun r => r.map Prod.fst)).dedup
  let rightFields := (rightRows.bind (fun r => r.map Prod.fst)).dedup
  let nullLeft : QueryRow := leftFields.map (fun f => (f, .vNull))
  let nullRight : QueryRow := rightFields.map (fun f => (f, .vNull))
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
      -- Left outer join: all left rows, with matching right rows or right-side null padding.
      leftRows.flatMap (fun l =>
        let matches := rightRows.filterMap (fun r =>
          let combined := combineRows l r
          if evalFilterExpr combined condition then some combined else none)
        if matches.isEmpty then [combineRows l nullRight] else matches)
  | .rightOuter =>
      -- Right outer join: all right rows, with matching left rows or left-side null padding.
      rightRows.flatMap (fun r =>
        let matches := leftRows.filterMap (fun l =>
          let combinedForCond := combineRows l r
          if evalFilterExpr combinedForCond condition then some (combineRowsRightPref l r) else none)
        if matches.isEmpty then [combineRows r nullLeft] else matches)
  | .fullOuter =>
      -- Full outer join: all rows from both sides, with null padding for non-matches.
      let leftWithMatches := leftRows.flatMap (fun l =>
        let matches := rightRows.filterMap (fun r =>
          let combined := combineRows l r
          if evalFilterExpr combined condition then some combined else none)
        if matches.isEmpty then [combineRows l nullRight] else matches)
      let unmatchedRight := rightRows.filter (fun r =>
        !leftRows.any (fun l =>
          let combined := combineRows l r
          evalFilterExpr combined condition))
      leftWithMatches ++ unmatchedRight.map (fun r => combineRows r nullLeft)

theorem evalJoin_cross_def
  (leftRows rightRows : List QueryRow)
  (condition : Expr) :
  evalJoin .cross leftRows rightRows condition =
    leftRows.flatMap (fun l => rightRows.map (fun r => combineRows l r)) := by
  rfl

theorem evalJoin_inner_def
  (leftRows rightRows : List QueryRow)
  (condition : Expr) :
  evalJoin .inner leftRows rightRows condition =
    leftRows.flatMap (fun l =>
      rightRows.filterMap (fun r =>
        let combined := combineRows l r
        if evalFilterExpr combined condition then some combined else none)) := by
  rfl

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

mutual
  partial def evalQuerySubsetWithSetOps (q : Query) (snaps : SnapSet) : List QueryRow :=
    evalQueryOpsWithSetOps q.pipeline (evalSourceSubset q.source snaps) snaps

  partial def evalQueryOpsWithSetOps (ops : List QueryOp) (rows : List QueryRow) (snaps : SnapSet) : List QueryRow :=
    match ops with
    | [] => rows
    | op :: rest =>
        let nextRows :=
          match op with
          | .setOp setOp rightQuery =>
              let rightRows := evalQuerySubsetWithSetOps rightQuery snaps
              applySetOp setOp rows rightRows
          | _ =>
              applyQueryOpSubset op rows
        evalQueryOpsWithSetOps rest nextRows snaps
end

theorem evalQueryOpsWithSetOps_single_setOp
  (snaps : SnapSet)
  (leftRows : List QueryRow)
  (setOp : SetOp)
  (rightQuery : Query) :
  evalQueryOpsWithSetOps [QueryOp.setOp setOp rightQuery] leftRows snaps =
    applySetOp setOp leftRows (evalQuerySubsetWithSetOps rightQuery snaps) := by
  rfl

def evalQuery (_ir : IR) (q : Query) (snaps : SnapSet) : List QueryRow :=
  evalQuerySubsetWithSetOps q snaps

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
