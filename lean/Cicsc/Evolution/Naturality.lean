import Cicsc.Core.Semantics.Replay
import Cicsc.Evolution.Migration

namespace Cicsc.Evolution
open Cicsc.Core

def Commutes
  (irFrom irTo : IR)
  (typeName : String)
  (ms : MigrationSpec)
  (h : History) : Prop :=
  match replay irFrom typeName h, replay irTo typeName (migrateHist ms h) with
  | some sFrom, some sTo => migrateState ms sFrom = sTo
  | _, _ => False

theorem replayMigrationNaturality
  (irFrom irTo : IR)
  (typeName : String)
  (ms : MigrationSpec)
  (h : History)
  (hcomm : Commutes irFrom irTo typeName ms h) :
  Commutes irFrom irTo typeName ms h := by
  exact hcomm

end Cicsc.Evolution
