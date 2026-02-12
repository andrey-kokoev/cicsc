import Cicsc.Core.Syntax
import Cicsc.Core.Types

namespace Cicsc.Core

def lookupField (xs : List (String × Val)) (k : String) : Val :=
  match xs.find? (fun (kv) => kv.fst = k) with
  | some kv => kv.snd
  | none => .vNull

def getPath (v : Val) (path : String) : Val :=
  match v with
  | .vObj fields => lookupField fields path
  | _ => .vNull

def hasPath (v : Val) (path : String) : Bool :=
  match v with
  | .vObj fields => (fields.find? (fun (kv) => kv.fst = path)).isSome
  | _ => false

def valEq : Val → Val → Bool
  | .vBool a, .vBool b => a = b
  | .vInt a, .vInt b => a = b
  | .vString a, .vString b => a = b
  | .vNull, .vNull => true
  | _, _ => false

def toBool : Val → Bool
  | .vBool b => b
  | .vInt n => n ≠ 0
  | .vString s => s.length > 0
  | .vNull => false
  | .vObj xs => !xs.isEmpty
  | .vArr xs => !xs.isEmpty

def evalVar (env : Env) : VarRef → Val
  | .now => .vInt (Int.ofNat env.now)
  | .actor => .vString env.actor
  | .state => .vString env.state
  | .input f => lookupField env.input f
  | .attrs f => lookupField env.attrs f
  | .row f => lookupField env.row f
  | .arg n => lookupField env.arg n
  | .rowsCount =>
      match env.rowsCount with
      | some n => .vInt (Int.ofNat n)
      | none => .vNull
  | .eType =>
      match env.eventCtx with
      | some e => .vString e.eType
      | none => .vNull
  | .eActor =>
      match env.eventCtx with
      | some e => .vString e.eActor
      | none => .vNull
  | .eTime =>
      match env.eventCtx with
      | some e => .vInt (Int.ofNat e.eTime)
      | none => .vNull
  | .ePayload p =>
      match env.eventCtx with
      | some e => getPath e.ePayload p
      | none => .vNull

partial def evalExpr (env : Env) : Expr → Val
  | .litBool b => .vBool b
  | .litInt n => .vInt n
  | .litString s => .vString s
  | .litNull => .vNull
  | .var v => evalVar env v
  | .get e path => getPath (evalExpr env e) path
  | .has e path => .vBool (hasPath (evalExpr env e) path)
  | .not e => .vBool (!(toBool (evalExpr env e)))
  | .and xs => .vBool (xs.all (fun e => toBool (evalExpr env e)))
  | .or xs => .vBool (xs.any (fun e => toBool (evalExpr env e)))
  | .eq a b => .vBool (valEq (evalExpr env a) (evalExpr env b))
  | .ne a b => .vBool (!(valEq (evalExpr env a) (evalExpr env b)))
  | .lt a b =>
      match evalExpr env a, evalExpr env b with
      | .vInt x, .vInt y => .vBool (x < y)
      | _, _ => .vNull
  | .le a b =>
      match evalExpr env a, evalExpr env b with
      | .vInt x, .vInt y => .vBool (x <= y)
      | _, _ => .vNull
  | .gt a b =>
      match evalExpr env a, evalExpr env b with
      | .vInt x, .vInt y => .vBool (x > y)
      | _, _ => .vNull
  | .ge a b =>
      match evalExpr env a, evalExpr env b with
      | .vInt x, .vInt y => .vBool (x >= y)
      | _, _ => .vNull
  | .add a b =>
      match evalExpr env a, evalExpr env b with
      | .vInt x, .vInt y => .vInt (x + y)
      | _, _ => .vNull
  | .sub a b =>
      match evalExpr env a, evalExpr env b with
      | .vInt x, .vInt y => .vInt (x - y)
      | _, _ => .vNull
  | .mul a b =>
      match evalExpr env a, evalExpr env b with
      | .vInt x, .vInt y => .vInt (x * y)
      | _, _ => .vNull
  | .div a b =>
      match evalExpr env a, evalExpr env b with
      | .vInt x, .vInt y =>
          if y = 0 then .vNull else .vInt (x / y)
      | _, _ => .vNull
  | .ifThenElse c t f =>
      if toBool (evalExpr env c) then evalExpr env t else evalExpr env f
  | .coalesce xs =>
      match xs.find? (fun e => evalExpr env e != .vNull) with
      | some e => evalExpr env e
      | none => .vNull
  | .call _fn _args => .vNull

theorem evalExprDeterministic (env : Env) (e : Expr) :
  ∀ v1 v2, evalExpr env e = v1 → evalExpr env e = v2 → v1 = v2 := by
  intro v1 v2 h1 h2
  simpa [h1] using h2

end Cicsc.Core
