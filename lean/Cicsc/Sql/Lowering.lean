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

end Cicsc.Sql
