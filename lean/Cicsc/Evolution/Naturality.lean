import Cicsc.Core.Semantics.Replay
import Cicsc.Evolution.Migration

namespace Cicsc.Evolution
open Cicsc.Core

def step (ir : IR) (typeName : String) (s : State) (e : Event) : Option State :=
  match lookupTypeSpec ir typeName with
  | none => none
  | some ts =>
      if e.entityType = typeName then
        some (applyReducer ts s e)
      else
        some s

def replayFromState (ir : IR) (typeName : String) (s : State) (h : History) : Option State :=
  h.foldl
    (fun acc e =>
      match acc with
      | none => none
      | some st => step ir typeName st e)
    (some s)

def stepMigrated (irTo : IR) (typeName : String) (ms : MigrationSpec) (s : State) (e : Event) : Option State :=
  match migrateEvent ms e with
  | none => some s
  | some e' => step irTo typeName s e'

def replayMigratedFromState
  (irTo : IR) (typeName : String) (ms : MigrationSpec) (s : State) (h : History) : Option State :=
  h.foldl
    (fun acc e =>
      match acc with
      | none => none
      | some st => stepMigrated irTo typeName ms st e)
    (some s)

def Commutes
  (irFrom irTo : IR)
  (typeName : String)
  (ms : MigrationSpec)
  (s0 : State)
  (h : History) : Prop :=
  replayMigratedFromState irTo typeName ms (migrateState ms s0) h =
    Option.map (migrateState ms) (replayFromState irFrom typeName s0 h)

def StepCommutes
  (irFrom irTo : IR)
  (typeName : String)
  (ms : MigrationSpec)
  : Prop :=
  ∀ (s s' : State) (e : Event),
    step irFrom typeName s e = some s' →
    stepMigrated irTo typeName ms (migrateState ms s) e = some (migrateState ms s')

theorem step_total_of_lookup
  (ir : IR)
  (typeName : String)
  (s : State)
  (e : Event)
  (hex : ∃ ts, lookupTypeSpec ir typeName = some ts) :
  ∃ s', step ir typeName s e = some s' := by
  rcases hex with ⟨ts, hts⟩
  unfold step
  by_cases heq : e.entityType = typeName
  · refine ⟨applyReducer ts s e, ?_⟩
    simp [hts, heq]
  · refine ⟨s, ?_⟩
    simp [hts, heq]

structure RestrictedMigrationClass
  (irFrom irTo : IR)
  (typeName : String)
  (ms : MigrationSpec) : Prop where
  wf : WFMigration ms irFrom irTo
  appliesToType : typeName = ms.entityType
  noPayload : NoPayloadTransforms ms
  stateRenameOnly : StateLabelRenamesOnly ms
  stepCommutes : StepCommutes irFrom irTo typeName ms

theorem replay_commutes
  (irFrom irTo : IR)
  (typeName : String)
  (ms : MigrationSpec)
  (hWf : WFMigration ms irFrom irTo)
  (happlies : typeName = ms.entityType)
  (hstep : StepCommutes irFrom irTo typeName ms) :
  ∀ (h : History) (s0 : State), Commutes irFrom irTo typeName ms s0 h := by
  have hsrc : ∃ ts, lookupTypeSpec irFrom typeName = some ts := by
    simpa [happlies] using wfMigration_sourceTypeExists ms irFrom irTo hWf
  intro h
  induction h with
  | nil =>
      intro s0
      unfold Commutes replayMigratedFromState replayFromState
      simp
  | cons e hs ih =>
      intro s0
      unfold Commutes replayMigratedFromState replayFromState
      rcases step_total_of_lookup irFrom typeName s0 e hsrc with ⟨s1, hstep0⟩
      have hmig :
        stepMigrated irTo typeName ms (migrateState ms s0) e = some (migrateState ms s1) :=
        hstep s0 s1 e hstep0
      simp [hstep0, hmig]
      exact ih s1

theorem replay_commutes_restricted
  (irFrom irTo : IR)
  (typeName : String)
  (ms : MigrationSpec)
  (hclass : RestrictedMigrationClass irFrom irTo typeName ms) :
  ∀ (h : History) (s0 : State), Commutes irFrom irTo typeName ms s0 h := by
  exact replay_commutes irFrom irTo typeName ms hclass.wf hclass.appliesToType hclass.stepCommutes

end Cicsc.Evolution
