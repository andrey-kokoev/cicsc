import Cicsc.Core.Syntax
import Cicsc.Core.Types

namespace Cicsc.Core

abbrev TypeEnv := List (String × Ty)

def lookupTy (Γ : TypeEnv) (k : String) : Option Ty :=
  match Γ.find? (fun kv => kv.fst = k) with
  | some kv => some kv.snd
  | none => none

partial def inferExprTy (Γ : TypeEnv) : Expr → Option Ty
  | .litBool _ => some .tBool
  | .litInt _ => some .tInt
  | .litString _ => some .tString
  | .litNull => some .tNull
  | .var (.input f) => lookupTy Γ s!"input.{f}"
  | .var (.attrs f) => lookupTy Γ s!"attrs.{f}"
  | .var (.row f) => lookupTy Γ s!"row.{f}"
  | .var (.arg f) => lookupTy Γ s!"arg.{f}"
  | .var _ => some .tString
  | .get _ _ => some .tObj
  | .has _ _ => some .tBool
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
      | x :: _ => inferExprTy Γ x
  | .call _ _ => some .tNull

def checkReducerOp (Γ : TypeEnv) : ReducerOp → Bool
  | .setState e => inferExprTy Γ e = some .tString
  | .setAttr _ e => (inferExprTy Γ e).isSome
  | .clearAttr _ => true
  | .setShadow _ e => (inferExprTy Γ e).isSome

def checkCommand (Γ : TypeEnv) (c : CommandSpec) : Bool :=
  inferExprTy Γ c.guard = some .tBool

def checkTypeSpec (ts : TypeSpec) : Bool :=
  let Γ : TypeEnv := []
  let okCommands := ts.commands.all (fun kv => checkCommand Γ kv.snd)
  let okReducers := ts.reducer.all (fun kv => kv.snd.all (checkReducerOp Γ))
  okCommands && okReducers

def checkIR (ir : IR) : Bool :=
  ir.types.all (fun kv => checkTypeSpec kv.snd)

inductive HasType : TypeEnv → Expr → Ty → Prop where
  | litBool (Γ : TypeEnv) (b : Bool) : HasType Γ (.litBool b) .tBool
  | litInt (Γ : TypeEnv) (n : Int) : HasType Γ (.litInt n) .tInt
  | litString (Γ : TypeEnv) (s : String) : HasType Γ (.litString s) .tString
  | varInput (Γ : TypeEnv) (f : String) (t : Ty)
      (h : lookupTy Γ s!"input.{f}" = some t) :
      HasType Γ (.var (.input f)) t
  | eq (Γ : TypeEnv) (a b : Expr) (t : Ty)
      (ha : HasType Γ a t) (hb : HasType Γ b t) :
      HasType Γ (.eq a b) .tBool
  | and (Γ : TypeEnv) (xs : List Expr)
      (h : ∀ e ∈ xs, HasType Γ e .tBool) :
      HasType Γ (.and xs) .tBool
  | not (Γ : TypeEnv) (e : Expr)
      (h : HasType Γ e .tBool) :
      HasType Γ (.not e) .tBool

def WellTypedEnv (Γ : TypeEnv) (env : Env) : Prop :=
  ∀ (k : String) (t : Ty), lookupTy Γ k = some t →
    let v := lookupField (env.input ++ env.attrs ++ env.row ++ env.arg) k
    valTy v = t ∨ v = .vNull

theorem lookupWellTypedNullOk
  (Γ : TypeEnv) (env : Env) (hEnv : WellTypedEnv Γ env) :
  ∀ k t, lookupTy Γ k = some t →
    let v := lookupField (env.input ++ env.attrs ++ env.row ++ env.arg) k
    valTy v = t ∨ v = .vNull := by
  intro k t hk
  exact hEnv k t hk

end Cicsc.Core
