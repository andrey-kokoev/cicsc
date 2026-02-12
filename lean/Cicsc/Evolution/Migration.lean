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

def eventCovered (ms : MigrationSpec) (eventType : String) : Prop :=
  ∃ t ∈ ms.transforms, t.source = eventType

def targetReducerExists (irTo : IR) (typeName targetEventType : String) : Prop :=
  ∃ ts ops, lookupTypeSpec irTo typeName = some ts ∧ (targetEventType, ops) ∈ ts.reducer

def targetStateValid (irTo : IR) (typeName targetState : String) : Prop :=
  ∃ ts, lookupTypeSpec irTo typeName = some ts ∧ targetState ∈ ts.states

def WFMigration (ms : MigrationSpec) (irFrom irTo : IR) : Prop :=
  ms.fromVersion = irFrom.version ∧
  ms.toVersion = irTo.version ∧
  (∀ et, et ∈ sourceEventTypes irFrom ms.entityType → eventCovered ms et) ∧
  (∀ tr, tr ∈ ms.transforms → tr.drop = false → targetReducerExists irTo ms.entityType tr.target) ∧
  (∀ kv, kv ∈ ms.stateMap → targetStateValid irTo ms.entityType kv.snd)

end Cicsc.Evolution
