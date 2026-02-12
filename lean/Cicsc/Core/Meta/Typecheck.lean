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

end Cicsc.Core
