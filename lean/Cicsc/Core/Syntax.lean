namespace Cicsc.Core

abbrev TypeName := String
abbrev EventType := String
abbrev AttrName := String
abbrev ShadowName := String

inductive VarRef where
  | now
  | actor
  | state
  | input (field : String)
  | attrs (field : String)
  | row (field : String)
  | rowState
  | arg (name : String)
  | rowsCount
  | eType
  | eActor
  | eTime
  | ePayload (path : String)
deriving Repr, DecidableEq

inductive Expr where
  | litBool (b : Bool)
  | litInt (n : Int)
  | litString (s : String)
  | litNull
  | var (v : VarRef)
  | get (e : Expr) (path : String)
  | has (e : Expr) (path : String)
  | not (e : Expr)
  | and (xs : List Expr)
  | or (xs : List Expr)
  | eq (a : Expr) (b : Expr)
  | ne (a : Expr) (b : Expr)
  | lt (a : Expr) (b : Expr)
  | le (a : Expr) (b : Expr)
  | gt (a : Expr) (b : Expr)
  | ge (a : Expr) (b : Expr)
  | add (a : Expr) (b : Expr)
  | sub (a : Expr) (b : Expr)
  | mul (a : Expr) (b : Expr)
  | div (a : Expr) (b : Expr)
  | ifThenElse (c : Expr) (t : Expr) (f : Expr)
  | coalesce (xs : List Expr)
  | call (fn : String) (args : List Expr)
deriving Repr, DecidableEq

structure EventSelector where
  name : String
  whereExpr : Option Expr := none
deriving Repr, DecidableEq

-- v2: Join types for relational algebra
-- See LEAN_KERNEL_V2.md §1.1.1
inductive JoinType where
  | inner
  | leftOuter
  | rightOuter
  | fullOuter
  | cross
deriving Repr, DecidableEq

inductive Source where
  | snap (typeName : TypeName)
  | slaStatus (name : String) (onType : TypeName)
  | join (joinType : JoinType) (left : Source) (right : Source) (condition : Expr)
deriving Repr, DecidableEq

structure ProjectField where
  name : String
  expr : Expr
deriving Repr, DecidableEq

structure GroupKey where
  name : String
  expr : Expr
deriving Repr, DecidableEq

inductive AggExpr where
  | count
  | sum (expr : Expr)
  | min (expr : Expr)
  | max (expr : Expr)
deriving Repr, DecidableEq

structure OrderKey where
  expr : Expr
  asc : Bool
deriving Repr, DecidableEq

inductive QueryOp where
  | filter (expr : Expr)
  | project (fields : List ProjectField)
  | groupBy (keys : List GroupKey) (aggs : List (String × AggExpr))
  | orderBy (keys : List OrderKey)
  | limit (n : Nat)
  | offset (n : Nat)
deriving Repr, DecidableEq

structure Query where
  source : Source
  pipeline : List QueryOp
deriving Repr, DecidableEq

-- v2: Query plan representation for optimization
-- See LEAN_KERNEL_V2.md §1.1.3

-- Join ordering hint for query optimization
inductive JoinOrder where
  | leftDeep   -- ((A ⋈ B) ⋈ C) ⋈ D
  | rightDeep  -- A ⋈ (B ⋈ (C ⋈ D))
  | bushy      -- (A ⋈ B) ⋈ (C ⋈ D)
  | specified (order : List Nat)  -- Explicit join order by source index
deriving Repr, DecidableEq

-- Physical plan hints for execution
structure PhysicalHints where
  joinOrder : JoinOrder := .leftDeep
  preferHashJoin : Bool := false
  estimatedSize : Option Nat := none
deriving Repr, DecidableEq

-- Logical query plan (source-level, pre-optimization)
structure LogicalPlan where
  sources : List Source
  conditions : List Expr
  operations : List QueryOp
deriving Repr, DecidableEq

-- Physical query plan (execution-level, post-optimization)
structure PhysicalPlan where
  logical : LogicalPlan
  hints : PhysicalHints
  selectedJoinTree : Source  -- Optimized join order
deriving Repr, DecidableEq

inductive ReducerOp where
  | setState (expr : Expr)
  | setAttr (name : AttrName) (expr : Expr)
  | clearAttr (name : AttrName)
  | setShadow (name : ShadowName) (expr : Expr)
deriving Repr, DecidableEq

structure CommandSpec where
  input : List (String × String)
  guard : Expr
  emits : List (EventType × List (String × Expr))
deriving Repr, DecidableEq

structure TypeSpec where
  idType : String
  states : List String
  initialState : String
  attrs : List (AttrName × String)
  shadows : List (ShadowName × String)
  commands : List (String × CommandSpec)
  reducer : List (EventType × List ReducerOp)
deriving Repr, DecidableEq

inductive Constraint where
  | snapshot (onType : TypeName) (expr : Expr)
  | boolQuery (onType : TypeName) (query : Query) (assertExpr : Expr)
deriving Repr, DecidableEq

structure ViewSpec where
  kind : String
  onType : TypeName
  query : Query
  rowPolicy : Option Expr := none
deriving Repr, DecidableEq

structure IR where
  version : Nat
  types : List (TypeName × TypeSpec)
  constraints : List (String × Constraint) := []
  views : List (String × ViewSpec) := []
deriving Repr, DecidableEq

end Cicsc.Core
