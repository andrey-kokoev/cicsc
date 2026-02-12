import Cicsc.Core.Semantics.Replay
import Cicsc.Evolution.Migration

namespace Cicsc.Evolution
open Cicsc.Core

def step (ir : IR) (sid : StreamId) (s : State) (e : Event) : Option State :=
  match lookupTypeSpec ir sid.entityType with
  | none => none
  | some ts =>
      if inStream sid e then
        some (applyReducer ts s e)
      else
        some s

def replayFromState (ir : IR) (sid : StreamId) (s : State) (h : History) : Option State :=
  h.foldl
    (fun acc e =>
      match acc with
      | none => none
      | some st => step ir sid st e)
    (some s)

def stepMigrated (irTo : IR) (sid : StreamId) (ms : MigrationSpec) (s : State) (e : Event) : Option State :=
  match migrateEvent ms e with
  | none => some s
  | some e' => step irTo sid s e'

def replayMigratedFromState
  (irTo : IR) (sid : StreamId) (ms : MigrationSpec) (s : State) (h : History) : Option State :=
  h.foldl
    (fun acc e =>
      match acc with
      | none => none
      | some st => stepMigrated irTo sid ms st e)
    (some s)

def Commutes
  (irFrom irTo : IR)
  (sid : StreamId)
  (ms : MigrationSpec)
  (s0 : State)
  (h : History) : Prop :=
  replayMigratedFromState irTo sid ms (migrateState ms s0) h =
    Option.map (migrateState ms) (replayFromState irFrom sid s0 h)

def StepCommutes
  (irFrom irTo : IR)
  (sid : StreamId)
  (ms : MigrationSpec)
  : Prop :=
  ∀ (s s' : State) (e : Event),
    step irFrom sid s e = some s' →
    stepMigrated irTo sid ms (migrateState ms s) e = some (migrateState ms s')

def ReducerCompatibility
  (irFrom irTo : IR)
  (sid : StreamId)
  (ms : MigrationSpec) : Prop :=
  ∀ (s : State) (e : Event),
    stepMigrated irTo sid ms (migrateState ms s) e =
      Option.map (migrateState ms) (step irFrom sid s e)

theorem stepCommutes_ofReducerCompatibility
  (irFrom irTo : IR)
  (sid : StreamId)
  (ms : MigrationSpec)
  (hcompat : ReducerCompatibility irFrom irTo sid ms) :
  StepCommutes irFrom irTo sid ms := by
  intro s s' e hstep
  have hcompat' := hcompat s e
  simp [hstep] at hcompat'
  exact hcompat'

theorem step_total_of_lookup
  (ir : IR)
  (sid : StreamId)
  (s : State)
  (e : Event)
  (hex : ∃ ts, lookupTypeSpec ir sid.entityType = some ts) :
  ∃ s', step ir sid s e = some s' := by
  rcases hex with ⟨ts, hts⟩
  unfold step
  by_cases heq : inStream sid e
  · refine ⟨applyReducer ts s e, ?_⟩
    simp [hts, heq]
  · refine ⟨s, ?_⟩
    simp [hts, heq]

structure RestrictedMigrationClass
  (irFrom irTo : IR)
  (sid : StreamId)
  (ms : MigrationSpec) : Prop where
  wf : WFMigration ms irFrom irTo
  appliesToType : sid.entityType = ms.entityType
  noPayload : NoPayloadTransforms ms
  stateRenameOnly : StateLabelRenamesOnly ms
  reducerCompatibility : ReducerCompatibility irFrom irTo sid ms

theorem replay_commutes
  (irFrom irTo : IR)
  (sid : StreamId)
  (ms : MigrationSpec)
  (hWf : WFMigration ms irFrom irTo)
  (happlies : sid.entityType = ms.entityType)
  (hcompat : ReducerCompatibility irFrom irTo sid ms) :
  ∀ (h : History) (s0 : State), Commutes irFrom irTo sid ms s0 h := by
  have hsrc : ∃ ts, lookupTypeSpec irFrom sid.entityType = some ts := by
    simpa [happlies] using wfMigration_sourceTypeExists ms irFrom irTo hWf
  have hstep : StepCommutes irFrom irTo sid ms :=
    stepCommutes_ofReducerCompatibility irFrom irTo sid ms hcompat
  intro h
  induction h with
  | nil =>
      intro s0
      unfold Commutes replayMigratedFromState replayFromState
      simp
  | cons e hs ih =>
      intro s0
      unfold Commutes replayMigratedFromState replayFromState
      rcases step_total_of_lookup irFrom sid s0 e hsrc with ⟨s1, hstep0⟩
      have hmig :
        stepMigrated irTo sid ms (migrateState ms s0) e = some (migrateState ms s1) :=
        hstep s0 s1 e hstep0
      simp [hstep0, hmig]
      exact ih s1

theorem replay_commutes_restricted
  (irFrom irTo : IR)
  (sid : StreamId)
  (ms : MigrationSpec)
  (hclass : RestrictedMigrationClass irFrom irTo sid ms) :
  ∀ (h : History) (s0 : State), Commutes irFrom irTo sid ms s0 h := by
  exact replay_commutes irFrom irTo sid ms hclass.wf hclass.appliesToType hclass.reducerCompatibility

end Cicsc.Evolution
