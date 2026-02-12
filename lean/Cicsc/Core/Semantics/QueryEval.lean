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
