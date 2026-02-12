import Cicsc.Sql.Ast
import Cicsc.Core.Semantics.QueryEval

namespace Cicsc.Sql
open Cicsc.Core

abbrev DB := List (String × List QueryRow)

def lookupTable (db : DB) (name : String) : List QueryRow :=
  match db.find? (fun kv => kv.fst = name) with
  | some (_, rows) => rows
  | none => []

partial def evalSQLExpr (row : QueryRow) : SQLExpr → Val
  | .litNull => .vNull
  | .litInt n => .vInt n
  | .litString s => .vString s
  | .litBool b => .vBool b
  | .column name => lookupField row name
  | .binOp op lhs rhs =>
      let lv := evalSQLExpr row lhs
      let rv := evalSQLExpr row rhs
      match op with
      | "=" => .vBool (valEq lv rv)
      | "!=" => .vBool (!(valEq lv rv))
      | "AND" => .vBool (toBool lv && toBool rv)
      | "OR" => .vBool (toBool lv || toBool rv)
      | "<" => .vBool (compare lv rv = .lt)
      | "<=" => .vBool (compare lv rv ≠ .gt)
      | ">" => .vBool (compare lv rv = .gt)
      | ">=" => .vBool (compare lv rv ≠ .lt)
      | "+" =>
          match lv, rv with
          | .vInt a, .vInt b => .vInt (a + b)
          | _, _ => .vNull
      | "-" =>
          match lv, rv with
          | .vInt a, .vInt b => .vInt (a - b)
          | _, _ => .vNull
      | "*" =>
          match lv, rv with
          | .vInt a, .vInt b => .vInt (a * b)
          | _, _ => .vNull
      | "/" =>
          match lv, rv with
          | .vInt a, .vInt b => if b = 0 then .vNull else .vInt (a / b)
          | _, _ => .vNull
      | _ => .vNull
  | .unOp op arg =>
      let v := evalSQLExpr row arg
      match op with
      | "NOT" => .vBool (!toBool v)
      | _ => .vNull
  | .func _name _args => .vNull
  | .caseWhen cond t e =>
      if toBool (evalSQLExpr row cond) then evalSQLExpr row t else evalSQLExpr row e

def evalSQLBool (row : QueryRow) (e : SQLExpr) : Bool :=
  toBool (evalSQLExpr row e)

partial def execFrom (from : SQLFrom) (db : DB) : List QueryRow :=
  match from with
  | .table name _ => lookupTable db name
  | .join joinType left right onExpr =>
      let leftRows := execFrom left db
      let rightRows := execFrom right db
      let cond : Expr :=
        match onExpr with
        | none => .litBool true
        | some _ => .litBool true
      let joined := evalJoin
        (match joinType with
         | .inner => .inner
         | .left => .leftOuter
         | .right => .rightOuter
         | .full => .fullOuter
         | .cross => .cross)
        leftRows rightRows cond
      match onExpr with
      | none => joined
      | some on => joined.filter (fun r => evalSQLBool r on)

def applySelect (rows : List QueryRow) (fields : List (String × SQLExpr)) : List QueryRow :=
  if fields = [("_row", .column "*")] then rows
  else
    rows.map (fun row => fields.map (fun (name, expr) => (name, evalSQLExpr row expr)))

def execSQL (q : SQLQuery) (db : DB) : List QueryRow :=
  let base := execFrom q.from db
  let filtered :=
    match q.whereClause with
    | none => base
    | some e => base.filter (fun r => evalSQLBool r e)
  let selected := applySelect filtered q.select
  let dropped := match q.offset with | none => selected | some n => selected.drop n
  match q.limit with
  | none => dropped
  | some n => dropped.take n

end Cicsc.Sql
