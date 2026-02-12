import Cicsc.Core.Syntax
import Cicsc.Core.Semantics.Common
import Cicsc.Core.Meta.Typecheck
import Cicsc.Core.Semantics.Replay

namespace Cicsc.Core

def NoReservedCollisions (ts : TypeSpec) : Prop :=
  hasReservedRowFieldCollision ts = false

def initialStateInStates (ts : TypeSpec) : Prop :=
  ts.initialState ∈ ts.states

def declaredAttrNames (ts : TypeSpec) : List String :=
  ts.attrs.map Prod.fst

def declaredShadowNames (ts : TypeSpec) : List String :=
  ts.shadows.map Prod.fst

def NoDuplicateFieldNames (ts : TypeSpec) : Prop :=
  hasDuplicateAttrNames ts = false ∧ hasDuplicateShadowNames ts = false

def reducerTargetsDeclared (ts : TypeSpec) : Prop :=
  checkReducerTargetsDeclared ts = true

def reducerLiteralStatesValid (ts : TypeSpec) : Prop :=
  checkReducerLiteralStatesValid ts = true

def reducerOpsTypecheck (ts : TypeSpec) : Prop :=
  match stateTypeEnv ts with
  | none => False
  | some Γstate =>
      ∀ evt ops, (evt, ops) ∈ ts.reducer →
        ∀ op ∈ ops, checkReducerOp Γstate op = true

def commandsTypecheck (ts : TypeSpec) : Prop :=
  match stateTypeEnv ts with
  | none => False
  | some Γstate =>
      ∀ name cmd, (name, cmd) ∈ ts.commands →
        ∃ Γcmd, commandTypeEnv ts cmd = some Γcmd ∧ checkCommand Γcmd cmd = true

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

theorem reducerOpsTypecheck_of_checkTypeSpec
  (ts : TypeSpec)
  (hcheck : checkTypeSpec ts = true) :
  reducerOpsTypecheck ts := by
  unfold checkTypeSpec at hcheck
  split at hcheck
  · contradiction
  · cases hState : stateTypeEnv ts with
    | none =>
        simp [hState] at hcheck
    | some Γstate =>
        simp [hState] at hcheck
        intro evt ops hmem op hop
        have hpair : (ops.all (checkReducerOp Γstate)) = true :=
          (List.all_eq_true.mp hcheck.2) (evt, ops) hmem
        exact (List.all_eq_true.mp hpair) op hop

theorem commandsTypecheck_of_checkTypeSpec
  (ts : TypeSpec)
  (hcheck : checkTypeSpec ts = true) :
  commandsTypecheck ts := by
  unfold checkTypeSpec at hcheck
  split at hcheck
  · contradiction
  · cases hState : stateTypeEnv ts with
    | none =>
        simp [hState] at hcheck
    | some Γstate =>
        simp [hState] at hcheck
        intro name cmd hmem
        have hcmd :
          (match commandTypeEnv ts cmd with
          | none => false
          | some Γcmd => checkCommand Γcmd cmd) = true :=
          (List.all_eq_true.mp hcheck.1) (name, cmd) hmem
        cases hΓ : commandTypeEnv ts cmd with
        | none =>
            simp [hΓ] at hcmd
        | some Γcmd =>
            exact ⟨Γcmd, hΓ, by simpa [hΓ] using hcmd⟩

theorem noReservedCollisions_of_checkTypeSpecNames
  (ts : TypeSpec)
  (hnames : checkTypeSpecNames ts = true) :
  NoReservedCollisions ts := by
  unfold checkTypeSpecNames at hnames
  simp [NoReservedCollisions] at hnames
  exact hnames.1

theorem noDuplicateFieldNames_of_checkTypeSpecNames
  (ts : TypeSpec)
  (hnames : checkTypeSpecNames ts = true) :
  NoDuplicateFieldNames ts := by
  unfold checkTypeSpecNames at hnames
  simp [NoDuplicateFieldNames] at hnames
  exact ⟨hnames.3.1, hnames.3.2⟩

theorem initialStateInStates_of_checkTypeSpec
  (ts : TypeSpec)
  (hcheck : checkTypeSpec ts = true) :
  initialStateInStates ts := by
  have hinit : checkInitialStateDeclared ts = true := by
    by_contra hni
    have hguard : !checkTypeSpecNames ts || !checkInitialStateDeclared ts ||
      !checkReducerTargetsDeclared ts || !checkReducerLiteralStatesValid ts = true := by
      simp [hni]
    simp [checkTypeSpec, hguard] at hcheck
  simpa [initialStateInStates, checkInitialStateDeclared] using hinit

theorem reducerTargetsDeclared_of_checkTypeSpec
  (ts : TypeSpec)
  (hcheck : checkTypeSpec ts = true) :
  reducerTargetsDeclared ts := by
  have htargets : checkReducerTargetsDeclared ts = true := by
    by_contra hnt
    have hguard : !checkTypeSpecNames ts || !checkInitialStateDeclared ts ||
      !checkReducerTargetsDeclared ts || !checkReducerLiteralStatesValid ts = true := by
      simp [hnt]
    simp [checkTypeSpec, hguard] at hcheck
  simpa [reducerTargetsDeclared] using htargets

theorem reducerLiteralStatesValid_of_checkTypeSpec
  (ts : TypeSpec)
  (hcheck : checkTypeSpec ts = true) :
  reducerLiteralStatesValid ts := by
  have hlit : checkReducerLiteralStatesValid ts = true := by
    by_contra hnl
    have hguard : !checkTypeSpecNames ts || !checkInitialStateDeclared ts ||
      !checkReducerTargetsDeclared ts || !checkReducerLiteralStatesValid ts = true := by
      simp [hnl]
    simp [checkTypeSpec, hguard] at hcheck
  simpa [reducerLiteralStatesValid] using hlit

theorem checkTypeSpecNames_of_checkTypeSpec
  (ts : TypeSpec)
  (hcheck : checkTypeSpec ts = true) :
  checkTypeSpecNames ts = true := by
  by_contra hnn
  have hguard : !checkTypeSpecNames ts || !checkInitialStateDeclared ts ||
      !checkReducerTargetsDeclared ts || !checkReducerLiteralStatesValid ts = true := by
    simp [hnn]
  simp [checkTypeSpec, hguard] at hcheck

theorem wfTypeSpec_of_checkTypeSpec
  (ts : TypeSpec)
  (hcheck : checkTypeSpec ts = true) :
  WFTypeSpec ts := by
  refine ⟨
    initialStateInStates_of_checkTypeSpec ts hcheck,
    noReservedCollisions_of_checkTypeSpecNames ts (checkTypeSpecNames_of_checkTypeSpec ts hcheck),
    noDuplicateFieldNames_of_checkTypeSpecNames ts (checkTypeSpecNames_of_checkTypeSpec ts hcheck),
    reducerTargetsDeclared_of_checkTypeSpec ts hcheck,
    reducerLiteralStatesValid_of_checkTypeSpec ts hcheck,
    reducerOpsTypecheck_of_checkTypeSpec ts hcheck,
    commandsTypecheck_of_checkTypeSpec ts hcheck
  ⟩

-- Coverage audit (v1.5/B.9):
-- Existing bridge lemmas connect `checkTypeSpec = true` to:
--   * `reducerOpsTypecheck ts`
--   * `commandsTypecheck ts`
-- Remaining `WFTypeSpec` conjuncts are bridged by dedicated lemmas added in
-- subsequent checkboxes (B.10-B.15).

end Cicsc.Core
