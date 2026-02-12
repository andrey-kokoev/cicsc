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

theorem lowerQueryOp_filter_correct (q : SQLQuery) (e : Expr) :
  lowerQueryOp q (.filter e) = { q with whereClause := appendWhere q.whereClause (lowerExpr e) } := by
  rfl

theorem lowerQueryOp_project_correct (q : SQLQuery) (fields : List ProjectField) :
  lowerQueryOp q (.project fields) = { q with select := fields.map (fun f => (f.name, lowerExpr f.expr)) } := by
  rfl

theorem lowerQueryOp_groupBy_correct (q : SQLQuery) (keys : List GroupKey) (aggs : List (String × AggExpr)) :
  lowerQueryOp q (.groupBy keys aggs) = { q with groupBy := keys.map (fun k => lowerExpr k.expr) } := by
  rfl

theorem lowerQueryOp_having_correct (q : SQLQuery) (e : Expr) :
  lowerQueryOp q (.having e) = { q with having := appendHaving q.having (lowerExpr e) } := by
  rfl

theorem lowerQueryOp_orderBy_correct (q : SQLQuery) (keys : List OrderKey) :
  lowerQueryOp q (.orderBy keys) = { q with orderBy := keys.map (fun k => { expr := lowerExpr k.expr, asc := k.asc }) } := by
  rfl

theorem lowerQueryOp_limit_correct (q : SQLQuery) (n : Nat) :
  lowerQueryOp q (.limit n) = { q with limit := some n } := by
  rfl

theorem lowerQueryOp_offset_correct (q : SQLQuery) (n : Nat) :
  lowerQueryOp q (.offset n) = { q with offset := some n } := by
  rfl

theorem lowerQuery_base (src : Source) :
  lowerQuery { source := src, pipeline := [] } =
    { select := [("_row", .column "*")], from := lowerSource src } := by
  rfl

theorem lowerExpr_litBool (b : Bool) :
  lowerExpr (.litBool b) = .litBool b := by
  rfl

theorem lowerExpr_litInt (n : Int) :
  lowerExpr (.litInt n) = .litInt n := by
  rfl

theorem lowerExpr_litString (s : String) :
  lowerExpr (.litString s) = .litString s := by
  rfl

theorem lowerExpr_litNull :
  lowerExpr .litNull = .litNull := by
  rfl

theorem lowerExpr_var (v : VarRef) :
  lowerExpr (.var v) = lowerVarRef v := by
  rfl

theorem lowerExpr_not (e : Expr) :
  lowerExpr (.not e) = .unOp "NOT" (lowerExpr e) := by
  rfl

theorem lowerExpr_and (xs : List Expr) :
  lowerExpr (.and xs) = xs.foldl (fun acc e => .binOp "AND" acc (lowerExpr e)) (.litBool true) := by
  rfl

theorem lowerExpr_or (xs : List Expr) :
  lowerExpr (.or xs) = xs.foldl (fun acc e => .binOp "OR" acc (lowerExpr e)) (.litBool false) := by
  rfl

theorem lowerExpr_eq (a b : Expr) :
  lowerExpr (.eq a b) = .binOp "=" (lowerExpr a) (lowerExpr b) := by
  rfl

theorem lowerExpr_ne (a b : Expr) :
  lowerExpr (.ne a b) = .binOp "!=" (lowerExpr a) (lowerExpr b) := by
  rfl

theorem lowerExpr_lt (a b : Expr) :
  lowerExpr (.lt a b) = .binOp "<" (lowerExpr a) (lowerExpr b) := by
  rfl

theorem lowerExpr_le (a b : Expr) :
  lowerExpr (.le a b) = .binOp "<=" (lowerExpr a) (lowerExpr b) := by
  rfl

theorem lowerExpr_gt (a b : Expr) :
  lowerExpr (.gt a b) = .binOp ">" (lowerExpr a) (lowerExpr b) := by
  rfl

theorem lowerExpr_ge (a b : Expr) :
  lowerExpr (.ge a b) = .binOp ">=" (lowerExpr a) (lowerExpr b) := by
  rfl

theorem lowerExpr_add (a b : Expr) :
  lowerExpr (.add a b) = .binOp "+" (lowerExpr a) (lowerExpr b) := by
  rfl

theorem lowerExpr_sub (a b : Expr) :
  lowerExpr (.sub a b) = .binOp "-" (lowerExpr a) (lowerExpr b) := by
  rfl

theorem lowerExpr_mul (a b : Expr) :
  lowerExpr (.mul a b) = .binOp "*" (lowerExpr a) (lowerExpr b) := by
  rfl

theorem lowerExpr_div (a b : Expr) :
  lowerExpr (.div a b) = .binOp "/" (lowerExpr a) (lowerExpr b) := by
  rfl

end Cicsc.Sql
