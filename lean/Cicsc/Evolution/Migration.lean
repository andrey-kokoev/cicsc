import Cicsc.Core.Types
import Cicsc.Core.Semantics.Replay

namespace Cicsc.Evolution
open Cicsc.Core

structure EventTransform where
  source : String
  target : String
  drop : Bool := false
deriving Repr, DecidableEq

structure MigrationSpec where
  fromVersion : Nat
  toVersion : Nat
  entityType : String
  transforms : List EventTransform
  stateMap : List (String × String)
deriving Repr, DecidableEq

def lookupTransform (ms : MigrationSpec) (eventType : String) : Option EventTransform :=
  ms.transforms.find? (fun t => t.source = eventType)

def migrateEvent (ms : MigrationSpec) (e : Event) : Option Event :=
  if e.entityType ≠ ms.entityType then
    some e
  else
    match lookupTransform ms e.eventType with
    | none => some e
    | some t =>
        if t.drop then none
        else some { e with eventType := t.target }

def migrateHist (ms : MigrationSpec) (h : History) : History :=
  (h.map (migrateEvent ms)).filterMap id

def migrateState (ms : MigrationSpec) (st : State) : State :=
  match ms.stateMap.find? (fun kv => kv.fst = st.st) with
  | some kv => { st with st := kv.snd }
  | none => st

def sourceEventTypes (irFrom : IR) (typeName : String) : List String :=
  match lookupTypeSpec irFrom typeName with
  | none => []
  | some ts => ts.reducer.map Prod.fst

def eventMapped (ms : MigrationSpec) (eventType : String) : Prop :=
  ∃ t ∈ ms.transforms, t.source = eventType ∧ t.drop = false

def eventDropped (ms : MigrationSpec) (eventType : String) : Prop :=
  ∃ t ∈ ms.transforms, t.source = eventType ∧ t.drop = true

def eventCoveredOrDropped (ms : MigrationSpec) (eventType : String) : Prop :=
  eventMapped ms eventType ∨ eventDropped ms eventType

def TotalOnTypeCoverage (ms : MigrationSpec) (irFrom : IR) : Prop :=
  ∀ et, et ∈ sourceEventTypes irFrom ms.entityType → eventCoveredOrDropped ms et

def targetReducerExists (irTo : IR) (typeName targetEventType : String) : Prop :=
  ∃ ts ops, lookupTypeSpec irTo typeName = some ts ∧ (targetEventType, ops) ∈ ts.reducer

def targetStateValid (irTo : IR) (typeName targetState : String) : Prop :=
  ∃ ts, lookupTypeSpec irTo typeName = some ts ∧ targetState ∈ ts.states

def WFMigration (ms : MigrationSpec) (irFrom irTo : IR) : Prop :=
  ms.fromVersion = irFrom.version ∧
  ms.toVersion = irTo.version ∧
  (∃ tsFrom, lookupTypeSpec irFrom ms.entityType = some tsFrom) ∧
  (∃ tsTo, lookupTypeSpec irTo ms.entityType = some tsTo) ∧
  (∀ tr, tr ∈ ms.transforms → tr.drop = false → targetReducerExists irTo ms.entityType tr.target) ∧
  (∀ kv, kv ∈ ms.stateMap → targetStateValid irTo ms.entityType kv.snd)

def WFMigrationStrict (ms : MigrationSpec) (irFrom irTo : IR) : Prop :=
  WFMigration ms irFrom irTo ∧ TotalOnTypeCoverage ms irFrom

theorem wfMigrationStrict_implies_wf
  (ms : MigrationSpec) (irFrom irTo : IR)
  (h : WFMigrationStrict ms irFrom irTo) :
  WFMigration ms irFrom irTo := by
  exact h.1

theorem wfMigration_sourceTypeExists
  (ms : MigrationSpec) (irFrom irTo : IR)
  (hWf : WFMigration ms irFrom irTo) :
  ∃ tsFrom, lookupTypeSpec irFrom ms.entityType = some tsFrom := by
  exact hWf.2.2.1

theorem wfMigration_targetTypeExists
  (ms : MigrationSpec) (irFrom irTo : IR)
  (hWf : WFMigration ms irFrom irTo) :
  ∃ tsTo, lookupTypeSpec irTo ms.entityType = some tsTo := by
  exact hWf.2.2.2.1

def NoPayloadTransforms (ms : MigrationSpec) : Prop :=
  ∀ e e', migrateEvent ms e = some e' → e'.payload = e.payload

theorem migrateEvent_noPayloadTransforms (ms : MigrationSpec) : NoPayloadTransforms ms := by
  intro e e' hmig
  unfold migrateEvent at hmig
  by_cases hent : e.entityType ≠ ms.entityType
  · simp [hent] at hmig
    cases hmig
    rfl
  · simp [hent] at hmig
    cases hfind : lookupTransform ms e.eventType with
    | none =>
        simp [hfind] at hmig
        cases hmig
        rfl
    | some t =>
        by_cases hdrop : t.drop
        · simp [hfind, hdrop] at hmig
        · simp [hfind, hdrop] at hmig
          cases hmig
          rfl

def StateLabelRenamesOnly (ms : MigrationSpec) : Prop :=
  ∀ st, (migrateState ms st).attrs = st.attrs ∧ (migrateState ms st).shadows = st.shadows

theorem migrateState_stateLabelRenamesOnly (ms : MigrationSpec) : StateLabelRenamesOnly ms := by
  intro st
  unfold migrateState
  split
  · simp
  · simp

end Cicsc.Evolution
