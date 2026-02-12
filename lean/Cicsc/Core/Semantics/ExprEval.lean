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

def evalExprFuel (env : Env) : Nat → Expr → Val
  | 0, _ => .vNull
  | Nat.succ fuel, .litBool b => .vBool b
  | Nat.succ fuel, .litInt n => .vInt n
  | Nat.succ fuel, .litString s => .vString s
  | Nat.succ fuel, .litNull => .vNull
  | Nat.succ fuel, .var v => evalVar env v
  | Nat.succ fuel, .get e path => getPath (evalExprFuel env fuel e) path
  | Nat.succ fuel, .has e path => .vBool (hasPath (evalExprFuel env fuel e) path)
  | Nat.succ fuel, .not e => .vBool (!(toBool (evalExprFuel env fuel e)))
  | Nat.succ fuel, .and xs => .vBool (xs.all (fun e => toBool (evalExprFuel env fuel e)))
  | Nat.succ fuel, .or xs => .vBool (xs.any (fun e => toBool (evalExprFuel env fuel e)))
  | Nat.succ fuel, .eq a b => .vBool (valEq (evalExprFuel env fuel a) (evalExprFuel env fuel b))
  | Nat.succ fuel, .ne a b => .vBool (!(valEq (evalExprFuel env fuel a) (evalExprFuel env fuel b)))
  | Nat.succ fuel, .lt a b =>
      match evalExprFuel env fuel a, evalExprFuel env fuel b with
      | .vInt x, .vInt y => .vBool (x < y)
      | _, _ => .vNull
  | Nat.succ fuel, .le a b =>
      match evalExprFuel env fuel a, evalExprFuel env fuel b with
      | .vInt x, .vInt y => .vBool (x <= y)
      | _, _ => .vNull
  | Nat.succ fuel, .gt a b =>
      match evalExprFuel env fuel a, evalExprFuel env fuel b with
      | .vInt x, .vInt y => .vBool (x > y)
      | _, _ => .vNull
  | Nat.succ fuel, .ge a b =>
      match evalExprFuel env fuel a, evalExprFuel env fuel b with
      | .vInt x, .vInt y => .vBool (x >= y)
      | _, _ => .vNull
  | Nat.succ fuel, .add a b =>
      match evalExprFuel env fuel a, evalExprFuel env fuel b with
      | .vInt x, .vInt y => .vInt (x + y)
      | _, _ => .vNull
  | Nat.succ fuel, .sub a b =>
      match evalExprFuel env fuel a, evalExprFuel env fuel b with
      | .vInt x, .vInt y => .vInt (x - y)
      | _, _ => .vNull
  | Nat.succ fuel, .mul a b =>
      match evalExprFuel env fuel a, evalExprFuel env fuel b with
      | .vInt x, .vInt y => .vInt (x * y)
      | _, _ => .vNull
  | Nat.succ fuel, .div a b =>
      match evalExprFuel env fuel a, evalExprFuel env fuel b with
      | .vInt x, .vInt y =>
          if y = 0 then .vNull else .vInt (x / y)
      | _, _ => .vNull
  | Nat.succ fuel, .ifThenElse c t f =>
      if toBool (evalExprFuel env fuel c) then evalExprFuel env fuel t else evalExprFuel env fuel f
  | Nat.succ fuel, .coalesce xs =>
      match xs.find? (fun e => evalExprFuel env fuel e != .vNull) with
      | some e => evalExprFuel env fuel e
      | none => .vNull
  | Nat.succ _, .call _fn _args => .vNull

def evalExpr (env : Env) (e : Expr) : Val :=
  evalExprFuel env (e.sizeOf + 1) e

theorem evalExprDeterministic (env : Env) (e : Expr) :
  ∀ v1 v2, evalExpr env e = v1 → evalExpr env e = v2 → v1 = v2 := by
  intro v1 v2 h1 h2
  simpa [h1] using h2

end Cicsc.Core
