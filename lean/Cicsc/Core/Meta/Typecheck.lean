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
  | _ => none

partial def inferExprTy (Γ : TypeEnv) : Expr → Option Ty
  | .litBool _ => some .tBool
  | .litInt _ => some .tInt
  | .litString _ => some .tString
  | .litNull => some .tNull
  | .var v =>
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
  | .get e _ =>
      match inferExprTy Γ e with
      | some .tObj => none
      | _ => none
  | .has e _ =>
      match inferExprTy Γ e with
      | some .tObj => some .tBool
      | _ => none
  | .not e =>
      match inferExprTy Γ e with
      | some .tBool => some .tBool
      | _ => none
  | .and xs =>
      if xs.all (fun e => inferExprTy Γ e = some .tBool) then some .tBool else none
  | .or xs =>
      if xs.all (fun e => inferExprTy Γ e = some .tBool) then some .tBool else none
  | .eq a b =>
      if inferExprTy Γ a = inferExprTy Γ b then some .tBool else none
  | .ne a b =>
      if inferExprTy Γ a = inferExprTy Γ b then some .tBool else none
  | .lt a b | .le a b | .gt a b | .ge a b =>
      if inferExprTy Γ a = some .tInt ∧ inferExprTy Γ b = some .tInt then some .tBool else none
  | .add a b | .sub a b | .mul a b | .div a b =>
      if inferExprTy Γ a = some .tInt ∧ inferExprTy Γ b = some .tInt then some .tInt else none
  | .ifThenElse c t f =>
      if inferExprTy Γ c = some .tBool ∧ inferExprTy Γ t = inferExprTy Γ f then inferExprTy Γ t else none
  | .coalesce xs =>
      match xs with
      | [] => none
      | x :: rest =>
          match inferExprTy Γ x with
          | none => none
          | some tx =>
              if rest.all (fun e => inferExprTy Γ e = some tx) then some tx else none
  | .call _ _ => none

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

def mkStateEnv (ts : TypeSpec) : Option TypeEnv :=
  let attrsRes :=
    ts.attrs.foldl
      (fun acc kv =>
        match acc, parseTyName kv.snd with
        | some env, some t => some ((.attrs kv.fst, t) :: env)
        | _, _ => none)
      (some [])
  match attrsRes with
  | none => none
  | some env =>
      ts.shadows.foldl
        (fun acc kv =>
          match acc, parseTyName kv.snd with
          | some env', some t => some ((.row kv.fst, t) :: env')
          | _, _ => none)
        (some env)

def checkTypeSpec (ts : TypeSpec) : Bool :=
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
    valTy v = t ∨ v = .vNull

theorem lookupWellTypedNullOk
  (Γ : TypeEnv) (env : Env) (hEnv : WellTypedEnv Γ env) :
  ∀ k t, lookupTy Γ k = some t →
    let v := lookupByKey env k
    valTy v = t ∨ v = .vNull := by
  intro k t hk
  exact hEnv k t hk

end Cicsc.Core
