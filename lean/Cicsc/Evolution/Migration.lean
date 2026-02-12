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

def composeEventTransform (m2 : MigrationSpec) (t1 : EventTransform) : EventTransform :=
  if t1.drop then
    t1
  else
    match lookupTransform m2 t1.target with
    | none => { t1 with target := t1.target }
    | some t2 =>
        if t2.drop then
          { source := t1.source, target := t2.target, drop := true }
        else
          { source := t1.source, target := t2.target, drop := false }

def composeStateMapEntry (m2 : MigrationSpec) (kv : String × String) : (String × String) :=
  match m2.stateMap.find? (fun kv2 => kv2.fst = kv.snd) with
  | none => kv
  | some kv2 => (kv.fst, kv2.snd)

def composeMigrations (m1 m2 : MigrationSpec) : MigrationSpec := {
  fromVersion := m1.fromVersion
  toVersion := m2.toVersion
  entityType := m1.entityType
  transforms := m1.transforms.map (composeEventTransform m2)
  stateMap := m1.stateMap.map (composeStateMapEntry m2)
}

def ComposeAssocCompatible (m1 m2 m3 : MigrationSpec) : Prop :=
  (m1.transforms.map (composeEventTransform m2)).map (composeEventTransform m3) =
    m1.transforms.map (composeEventTransform (composeMigrations m2 m3)) ∧
  (m1.stateMap.map (composeStateMapEntry m2)).map (composeStateMapEntry m3) =
    m1.stateMap.map (composeStateMapEntry (composeMigrations m2 m3))

theorem composeMigrations_assoc_of_compatible
  (m1 m2 m3 : MigrationSpec)
  (hcompat : ComposeAssocCompatible m1 m2 m3)
  (htype : m1.entityType = m2.entityType ∧ m2.entityType = m3.entityType) :
  composeMigrations (composeMigrations m1 m2) m3 =
    composeMigrations m1 (composeMigrations m2 m3) := by
  rcases hcompat with ⟨htr, hst⟩
  rcases htype with ⟨h12, h23⟩
  cases m1
  cases m2
  cases m3
  simp [composeMigrations] at htr hst ⊢
  constructor
  · exact htr
  constructor
  · exact hst
  · exact h12.trans h23

def MigrationsCommuteOnHistory (m1 m2 : MigrationSpec) (h : History) : Prop :=
  migrateHist (composeMigrations m1 m2) h = migrateHist (composeMigrations m2 m1) h

def MigrationsCommute (m1 m2 : MigrationSpec) : Prop :=
  ∀ h, MigrationsCommuteOnHistory m1 m2 h

theorem migrations_commute_of_equal_compose
  (m1 m2 : MigrationSpec)
  (hcompose : composeMigrations m1 m2 = composeMigrations m2 m1) :
  MigrationsCommute m1 m2 := by
  intro h
  unfold MigrationsCommuteOnHistory
  simpa [hcompose]

def invertEventTransform (t : EventTransform) : EventTransform :=
  { source := t.target, target := t.source, drop := false }

def invertStateMapEntry (kv : String × String) : (String × String) :=
  (kv.snd, kv.fst)

def inverseMigration (ms : MigrationSpec) : Option MigrationSpec :=
  if ms.transforms.all (fun t => !t.drop) then
    some {
      fromVersion := ms.toVersion
      toVersion := ms.fromVersion
      entityType := ms.entityType
      transforms := ms.transforms.map invertEventTransform
      stateMap := ms.stateMap.map invertStateMapEntry
    }
  else
    none

theorem inverseMigration_exists_of_reversible
  (ms : MigrationSpec)
  (hreversible : ms.transforms.all (fun t => !t.drop) = true) :
  ∃ inv, inverseMigration ms = some inv := by
  unfold inverseMigration
  simp [hreversible]

end Cicsc.Evolution
