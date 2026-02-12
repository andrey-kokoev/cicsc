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
    | none => none
    | some t =>
        if t.drop then none
        else some { e with eventType := t.target }

def migrateHist (ms : MigrationSpec) (h : History) : History :=
  (h.map (migrateEvent ms)).filterMap id

def migrateState (ms : MigrationSpec) (st : State) : State :=
  match ms.stateMap.find? (fun kv => kv.fst = st.st) with
  | some kv => { st with st := kv.snd }
  | none => st

end Cicsc.Evolution
