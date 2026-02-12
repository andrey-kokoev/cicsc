import Cicsc.Core.Semantics.Replay

namespace Cicsc.Core

def visibleAtSeq (sid : StreamId) (cutoffSeq : Nat) (e : Event) : Bool :=
  inStream sid e && e.seq ≤ cutoffSeq

def snapshotAt (ir : IR) (sid : StreamId) (h : History) (cutoffSeq : Nat) : Option State :=
  replay ir sid (h.filter (visibleAtSeq sid cutoffSeq))

theorem snapshotAt_def
  (ir : IR)
  (sid : StreamId)
  (h : History)
  (cutoffSeq : Nat) :
  snapshotAt ir sid h cutoffSeq =
    replay ir sid (h.filter (visibleAtSeq sid cutoffSeq)) := by
  rfl

end Cicsc.Core
