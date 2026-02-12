import Cicsc.Core.Syntax
import Cicsc.Core.Types

namespace Cicsc.Core

inductive VarKey where
  | input (field : String)
  | attrs (field : String)
  | row (field : String)
  | arg (name : String)
deriving Repr, DecidableEq

abbrev TypeEnv := List (VarKey × Ty)

def lookupTy (Γ : TypeEnv) (k : VarKey) : Option Ty :=
  match Γ.find? (fun kv => kv.fst = k) with
  | some kv => some kv.snd
  | none => none

def varKeyOfRef : VarRef → Option VarKey
  | .input f => some (.input f)
  | .attrs f => some (.attrs f)
  | .row f => some (.row f)
  | .arg f => some (.arg f)
  | _ => none

def parseTyName : String → Option Ty
  | "bool" => some .tBool
  | "int" => some .tInt
  | "string" => some .tString
  | "null" => some .tNull
  | "obj" => some .tObj
  | "arr" => some .tArr
  | "dyn" => some .tDyn
  | _ => none

def inferExprTyFuel (Γ : TypeEnv) : Nat → Expr → Option Ty
  | 0, _ => none
  | Nat.succ fuel, .litBool _ => some .tBool
  | Nat.succ fuel, .litInt _ => some .tInt
  | Nat.succ fuel, .litString _ => some .tString
  | Nat.succ fuel, .litNull => some .tNull
  | Nat.succ fuel, .var v =>
      match varKeyOfRef v with
      | some k => lookupTy Γ k
      | none =>
          match v with
          | .now => some .tInt
          | .actor => some .tString
          | .state => some .tString
          | .rowsCount => some .tInt
          | .eType => some .tString
          | .eActor => some .tString
          | .eTime => some .tInt
          | .ePayload _ => none
  | Nat.succ fuel, .get e _ =>
      match inferExprTyFuel Γ fuel e with
      | some .tObj => some .tDyn
      | _ => none
  | Nat.succ fuel, .has e _ =>
      match inferExprTyFuel Γ fuel e with
      | some .tObj => some .tBool
      | _ => none
  | Nat.succ fuel, .not e =>
      match inferExprTyFuel Γ fuel e with
      | some .tBool => some .tBool
      | _ => none
  | Nat.succ fuel, .and xs =>
      if xs.all (fun e => inferExprTyFuel Γ fuel e = some .tBool) then some .tBool else none
  | Nat.succ fuel, .or xs =>
      if xs.all (fun e => inferExprTyFuel Γ fuel e = some .tBool) then some .tBool else none
  | Nat.succ fuel, .eq a b =>
      match inferExprTyFuel Γ fuel a, inferExprTyFuel Γ fuel b with
      | some ta, some tb =>
          if ta = tb ∨ ta = .tDyn ∨ tb = .tDyn then some .tBool else none
      | _, _ => none
  | Nat.succ fuel, .ne a b =>
      match inferExprTyFuel Γ fuel a, inferExprTyFuel Γ fuel b with
      | some ta, some tb =>
          if ta = tb ∨ ta = .tDyn ∨ tb = .tDyn then some .tBool else none
      | _, _ => none
  | Nat.succ fuel, .lt a b
  | Nat.succ fuel, .le a b
  | Nat.succ fuel, .gt a b
  | Nat.succ fuel, .ge a b =>
      if inferExprTyFuel Γ fuel a = some .tInt ∧ inferExprTyFuel Γ fuel b = some .tInt then
        some .tBool
      else
        none
  | Nat.succ fuel, .add a b
  | Nat.succ fuel, .sub a b
  | Nat.succ fuel, .mul a b
  | Nat.succ fuel, .div a b =>
      if inferExprTyFuel Γ fuel a = some .tInt ∧ inferExprTyFuel Γ fuel b = some .tInt then
        some .tInt
      else
        none
  | Nat.succ fuel, .ifThenElse c t f =>
      if inferExprTyFuel Γ fuel c = some .tBool ∧ inferExprTyFuel Γ fuel t = inferExprTyFuel Γ fuel f then
        inferExprTyFuel Γ fuel t
      else
        none
  | Nat.succ fuel, .coalesce xs =>
      match xs with
      | [] => none
      | x :: rest =>
          match inferExprTyFuel Γ fuel x with
          | none => none
          | some tx =>
              if rest.all (fun e => inferExprTyFuel Γ fuel e = some tx) then some tx else none
  | Nat.succ _, .call _ _ => none

def inferExprTy (Γ : TypeEnv) (e : Expr) : Option Ty :=
  inferExprTyFuel Γ (e.sizeOf + 1) e

def checkReducerOp (Γ : TypeEnv) : ReducerOp → Bool
  | .setState e => inferExprTy Γ e = some .tString
  | .setAttr _ e => (inferExprTy Γ e).isSome
  | .clearAttr _ => true
  | .setShadow _ e => (inferExprTy Γ e).isSome

def checkCommand (Γ : TypeEnv) (c : CommandSpec) : Bool :=
  inferExprTy Γ c.guard = some .tBool &&
  c.emits.all (fun e =>
    e.snd.all (fun kv => (inferExprTy Γ kv.snd).isSome))

def mkInputEnv (inputs : List (String × String)) : Option TypeEnv :=
  inputs.foldl
    (fun acc kv =>
      match acc, parseTyName kv.snd with
      | some env, some t => some ((.input kv.fst, t) :: env)
      | _, _ => none)
    (some [])

def hasReservedStateName (ts : TypeSpec) : Bool :=
  ts.attrs.any (fun kv => kv.fst = "state") ||
  ts.shadows.any (fun kv => kv.fst = "state")

def hasRowNameCollision (ts : TypeSpec) : Bool :=
  ts.attrs.any (fun a => ts.shadows.any (fun s => s.fst = a.fst))

def mkStateEnv (ts : TypeSpec) : Option TypeEnv :=
  let attrsOnlyRes :=
    ts.attrs.foldl
      (fun acc kv =>
        match acc, parseTyName kv.snd with
        | some env, some t => some ((.attrs kv.fst, t) :: env)
        | _, _ => none)
      (some [])
  match attrsOnlyRes with
  | none => none
  | some attrsOnly =>
      let rowWithAttrsRes :=
        ts.attrs.foldl
          (fun acc kv =>
            match acc, parseTyName kv.snd with
            | some env, some t => some ((.row kv.fst, t) :: env)
            | _, _ => none)
          (some attrsOnly)
      match rowWithAttrsRes with
      | none => none
      | some rowWithAttrs =>
          let rowWithShadowsRes :=
            ts.shadows.foldl
              (fun acc kv =>
                match acc, parseTyName kv.snd with
                | some env, some t => some ((.row kv.fst, t) :: env)
                | _, _ => none)
              (some rowWithAttrs)
          match rowWithShadowsRes with
          | none => none
          | some env => some ((.row "state", .tString) :: env)

def checkTypeSpecNames (ts : TypeSpec) : Bool :=
  !hasReservedStateName ts && !hasRowNameCollision ts

def checkTypeSpec (ts : TypeSpec) : Bool :=
  if !checkTypeSpecNames ts then
    false
  else
    match mkStateEnv ts with
    | none => false
    | some Γstate =>
        let okCommands := ts.commands.all (fun kv =>
          match mkInputEnv kv.snd.input with
          | none => false
          | some Γinput => checkCommand (Γinput ++ Γstate) kv.snd)
        let okReducers := ts.reducer.all (fun kv => kv.snd.all (checkReducerOp Γstate))
        okCommands && okReducers

def checkIR (ir : IR) : Bool :=
  ir.types.all (fun kv => checkTypeSpec kv.snd)

inductive HasType : TypeEnv → Expr → Ty → Prop where
  | litBool (Γ : TypeEnv) (b : Bool) : HasType Γ (.litBool b) .tBool
  | litInt (Γ : TypeEnv) (n : Int) : HasType Γ (.litInt n) .tInt
  | litString (Γ : TypeEnv) (s : String) : HasType Γ (.litString s) .tString
  | varInput (Γ : TypeEnv) (f : String) (t : Ty)
      (h : lookupTy Γ (.input f) = some t) :
      HasType Γ (.var (.input f)) t
  | varAttrs (Γ : TypeEnv) (f : String) (t : Ty)
      (h : lookupTy Γ (.attrs f) = some t) :
      HasType Γ (.var (.attrs f)) t
  | varRow (Γ : TypeEnv) (f : String) (t : Ty)
      (h : lookupTy Γ (.row f) = some t) :
      HasType Γ (.var (.row f)) t
  | varArg (Γ : TypeEnv) (f : String) (t : Ty)
      (h : lookupTy Γ (.arg f) = some t) :
      HasType Γ (.var (.arg f)) t
  | eq (Γ : TypeEnv) (a b : Expr) (t : Ty)
      (ha : HasType Γ a t) (hb : HasType Γ b t) :
      HasType Γ (.eq a b) .tBool
  | and (Γ : TypeEnv) (xs : List Expr)
      (h : ∀ e ∈ xs, HasType Γ e .tBool) :
      HasType Γ (.and xs) .tBool
  | not (Γ : TypeEnv) (e : Expr)
      (h : HasType Γ e .tBool) :
      HasType Γ (.not e) .tBool

def lookupByKey (env : Env) : VarKey → Val
  | .input f => lookupField env.input f
  | .attrs f => lookupField env.attrs f
  | .row f => lookupField env.row f
  | .arg f => lookupField env.arg f

def WellTypedEnv (Γ : TypeEnv) (env : Env) : Prop :=
  ∀ (k : VarKey) (t : Ty), lookupTy Γ k = some t →
    let v := lookupByKey env k
    valTy v = t ∨ t = .tDyn ∨ v = .vNull

theorem lookupWellTypedNullOk
  (Γ : TypeEnv) (env : Env) (hEnv : WellTypedEnv Γ env) :
  ∀ k t, lookupTy Γ k = some t →
    let v := lookupByKey env k
    valTy v = t ∨ t = .tDyn ∨ v = .vNull := by
  intro k t hk
  exact hEnv k t hk

end Cicsc.Core
