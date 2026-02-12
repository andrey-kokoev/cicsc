import Cicsc.Core.Syntax
import Cicsc.Core.Semantics.Common
import Cicsc.Core.Meta.Typecheck
import Cicsc.Core.Semantics.Replay

namespace Cicsc.Core

def NoReservedCollisions (ts : TypeSpec) : Prop :=
  (∀ kv ∈ ts.attrs, kv.fst ∉ ReservedRowKeys) ∧
  (∀ kv ∈ ts.shadows, kv.fst ∉ ReservedRowKeys)

def initialStateInStates (ts : TypeSpec) : Prop :=
  ts.initialState ∈ ts.states

def declaredAttrNames (ts : TypeSpec) : List String :=
  ts.attrs.map Prod.fst

def declaredShadowNames (ts : TypeSpec) : List String :=
  ts.shadows.map Prod.fst

def NoDuplicateFieldNames (ts : TypeSpec) : Prop :=
  (declaredAttrNames ts).Nodup ∧ (declaredShadowNames ts).Nodup

def reducerTargetsDeclared (ts : TypeSpec) : Prop :=
  ∀ evt ops, (evt, ops) ∈ ts.reducer →
    ∀ op ∈ ops,
      match op with
      | .setAttr name _ => name ∈ declaredAttrNames ts
      | .clearAttr name => name ∈ declaredAttrNames ts
      | .setShadow name _ => name ∈ declaredShadowNames ts
      | .setState _ => True

def reducerLiteralStatesValid (ts : TypeSpec) : Prop :=
  ∀ evt ops, (evt, ops) ∈ ts.reducer →
    ∀ op ∈ ops,
      match op with
      | .setState (.litString s) => s ∈ ts.states
      | .setState _ => True
      | _ => True

def reducerOpsTypecheck (ts : TypeSpec) : Prop :=
  match mkStateEnv ts with
  | none => False
  | some Γstate =>
      ts.reducer.all (fun kv => kv.snd.all (checkReducerOp Γstate)) = true

def commandsTypecheck (ts : TypeSpec) : Prop :=
  match mkStateEnv ts with
  | none => False
  | some Γstate =>
      ts.commands.all (fun kv =>
        match mkInputEnv kv.snd.input with
        | none => false
        | some Γinput => checkCommand (Γinput ++ Γstate) kv.snd) = true

def WFTypeSpec (ts : TypeSpec) : Prop :=
  initialStateInStates ts ∧
  NoReservedCollisions ts ∧
  NoDuplicateFieldNames ts ∧
  reducerTargetsDeclared ts ∧
  reducerLiteralStatesValid ts ∧
  reducerOpsTypecheck ts ∧
  commandsTypecheck ts

def typeExists (ir : IR) (typeName : String) : Prop :=
  ∃ ts, lookupTypeSpec ir typeName = some ts

def constraintsReferenceExistingTypes (ir : IR) : Prop :=
  ∀ name c, (name, c) ∈ ir.constraints →
    match c with
    | .snapshot onType _ => typeExists ir onType
    | .boolQuery onType _ _ => typeExists ir onType

def viewsReferenceExistingTypes (ir : IR) : Prop :=
  ∀ name v, (name, v) ∈ ir.views → typeExists ir v.onType

def WFIR (ir : IR) : Prop :=
  (∀ typeName ts, (typeName, ts) ∈ ir.types → WFTypeSpec ts) ∧
  constraintsReferenceExistingTypes ir ∧
  viewsReferenceExistingTypes ir

end Cicsc.Core
