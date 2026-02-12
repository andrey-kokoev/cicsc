import Cicsc.Core.Syntax
import Cicsc.Sql.Ast

namespace Cicsc.Sql
open Cicsc.Core

def lowerVarRef : VarRef → SQLExpr
  | .now => .column "_now"
  | .actor => .column "_actor"
  | .state => .column "state"
  | .input f => .column s!"input_{f}"
  | .attrs f => .column s!"attrs_{f}"
  | .row f => .column f
  | .rowState => .column "state"
  | .arg name => .column s!"arg_{name}"
  | .rowsCount => .column "rows_count"
  | .eType => .column "_event_type"
  | .eActor => .column "_event_actor"
  | .eTime => .column "_event_time"
  | .ePayload p => .func "json_extract" [.column "payload_json", .litString s!"$.{p}"]

partial def lowerExpr : Expr → SQLExpr
  | .litBool b => .litBool b
  | .litInt n => .litInt n
  | .litString s => .litString s
  | .litNull => .litNull
  | .var v => lowerVarRef v
  | .get e p => .func "json_extract" [lowerExpr e, .litString s!"$.{p}"]
  | .has e p => .binOp "IS NOT" (.func "json_extract" [lowerExpr e, .litString s!"$.{p}"]) .litNull
  | .not e => .unOp "NOT" (lowerExpr e)
  | .and xs => xs.foldl (fun acc e => .binOp "AND" acc (lowerExpr e)) (.litBool true)
  | .or xs => xs.foldl (fun acc e => .binOp "OR" acc (lowerExpr e)) (.litBool false)
  | .eq a b => .binOp "=" (lowerExpr a) (lowerExpr b)
  | .ne a b => .binOp "!=" (lowerExpr a) (lowerExpr b)
  | .lt a b => .binOp "<" (lowerExpr a) (lowerExpr b)
  | .le a b => .binOp "<=" (lowerExpr a) (lowerExpr b)
  | .gt a b => .binOp ">" (lowerExpr a) (lowerExpr b)
  | .ge a b => .binOp ">=" (lowerExpr a) (lowerExpr b)
  | .add a b => .binOp "+" (lowerExpr a) (lowerExpr b)
  | .sub a b => .binOp "-" (lowerExpr a) (lowerExpr b)
  | .mul a b => .binOp "*" (lowerExpr a) (lowerExpr b)
  | .div a b => .binOp "/" (lowerExpr a) (lowerExpr b)
  | .ifThenElse c t f => .caseWhen (lowerExpr c) (lowerExpr t) (lowerExpr f)
  | .coalesce xs => .func "coalesce" (xs.map lowerExpr)
  | .call fn args => .func fn (args.map lowerExpr)

def lowerJoinType : JoinType → SQLJoinType
  | .inner => .inner
  | .leftOuter => .left
  | .rightOuter => .right
  | .fullOuter => .full
  | .cross => .cross

partial def lowerSource : Source → SQLFrom
  | .snap _typeName => .table "snapshots_v0"
  | .slaStatus name _onType => .table s!"sla_status_{name}"
  | .join jt left right onExpr =>
      let onClause :=
        match jt with
        | .cross => none
        | _ => some (lowerExpr onExpr)
      .join (lowerJoinType jt) (lowerSource left) (lowerSource right) onClause

def sqlAnd (a b : SQLExpr) : SQLExpr :=
  .binOp "AND" a b

def appendWhere (w : Option SQLExpr) (e : SQLExpr) : Option SQLExpr :=
  match w with
  | none => some e
  | some w0 => some (sqlAnd w0 e)

def appendHaving (h : Option SQLExpr) (e : SQLExpr) : Option SQLExpr :=
  match h with
  | none => some e
  | some h0 => some (sqlAnd h0 e)

def lowerQueryOp (q : SQLQuery) (op : QueryOp) : SQLQuery :=
  match op with
  | .filter e => { q with whereClause := appendWhere q.whereClause (lowerExpr e) }
  | .project fields =>
      { q with select := fields.map (fun f => (f.name, lowerExpr f.expr)) }
  | .groupBy keys _aggs =>
      { q with groupBy := keys.map (fun k => lowerExpr k.expr) }
  | .having e =>
      { q with having := appendHaving q.having (lowerExpr e) }
  | .orderBy keys =>
      { q with orderBy := keys.map (fun k => { expr := lowerExpr k.expr, asc := k.asc }) }
  | .limit n =>
      { q with limit := some n }
  | .offset n =>
      { q with offset := some n }
  | .setOp _ _ =>
      q

def lowerQuery (q : Query) : SQLQuery :=
  q.pipeline.foldl lowerQueryOp {
    select := [("_row", .column "*")]
    from := lowerSource q.source
  }

end Cicsc.Sql
