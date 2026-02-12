import Cicsc.Core.Syntax

namespace Cicsc.Sql
open Cicsc.Core

inductive SQLExpr where
  | litNull
  | litInt (n : Int)
  | litString (s : String)
  | litBool (b : Bool)
  | column (name : String)
  | binOp (op : String) (lhs rhs : SQLExpr)
  | unOp (op : String) (arg : SQLExpr)
  | func (name : String) (args : List SQLExpr)
  | caseWhen (cond thenExpr elseExpr : SQLExpr)
deriving Repr, DecidableEq

structure SQLOrderBy where
  expr : SQLExpr
  asc : Bool := true
deriving Repr, DecidableEq

inductive SQLJoinType where
  | inner
  | left
  | right
  | full
  | cross
deriving Repr, DecidableEq

mutual
  inductive SQLFrom where
    | table (name : String) (alias : Option String := none)
    | join (joinType : SQLJoinType) (left right : SQLFrom) (on : Option SQLExpr := none)
  deriving Repr, DecidableEq

  structure SQLQuery where
    select : List (String × SQLExpr)
    from : SQLFrom
    whereClause : Option SQLExpr := none
    groupBy : List SQLExpr := []
    having : Option SQLExpr := none
    orderBy : List SQLOrderBy := []
    limit : Option Nat := none
    offset : Option Nat := none
  deriving Repr, DecidableEq
end

end Cicsc.Sql
