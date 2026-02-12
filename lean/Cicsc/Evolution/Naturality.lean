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

structure RestrictedMigrationClass
  (irFrom irTo : IR)
  (typeName : String)
  (ms : MigrationSpec) : Prop where
  wf : WFMigration ms irFrom irTo
  noPayload : NoPayloadTransforms ms
  stateRenameOnly : StateLabelRenamesOnly ms
  stepCommutes : StepCommutes irFrom irTo typeName ms

theorem replay_commutes
  (irFrom irTo : IR)
  (typeName : String)
  (ms : MigrationSpec)
  (_hWf : WFMigration ms irFrom irTo)
  (hstep : StepCommutes irFrom irTo typeName ms) :
  ∀ (h : History) (s0 : State), Commutes irFrom irTo typeName ms s0 h := by
  intro h
  induction h with
  | nil =>
      intro s0
      unfold Commutes replayMigratedFromState replayFromState
      simp
  | cons e hs ih =>
      intro s0
      unfold Commutes replayMigratedFromState replayFromState
      cases hstep0 : step irFrom typeName s0 e with
      | none =>
          simp [hstep0]
      | some s1 =>
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
  exact replay_commutes irFrom irTo typeName ms hclass.wf hclass.stepCommutes

end Cicsc.Evolution
