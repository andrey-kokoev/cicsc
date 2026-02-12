import Cicsc.Core.Semantics.Replay

namespace Cicsc.Core

inductive IsolationLevel where
  | readCommitted
  | snapshot
  | serializable
deriving Repr, DecidableEq

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

structure Transaction where
  sid : StreamId
  isolation : IsolationLevel
  beginSeq : Nat
  commitSeq : Nat
  writes : History := []
deriving Repr, DecidableEq

def readCutoff (tx : Transaction) : Nat :=
  match tx.isolation with
  | .readCommitted => tx.commitSeq
  | .snapshot => tx.beginSeq
  | .serializable => tx.beginSeq

def readSnapshot (ir : IR) (h : History) (tx : Transaction) : Option State :=
  snapshotAt ir tx.sid h (readCutoff tx)

def appendWrites (h : History) (tx : Transaction) : History :=
  h ++ tx.writes

def TxExecRel (_ir : IR) (h : History) (tx : Transaction) (h' : History) : Prop :=
  h' = appendWrites h tx ∧
  (∀ e ∈ tx.writes, inStream tx.sid e = true ∧ tx.beginSeq < e.seq)

theorem txExecRel_appends
  (ir : IR)
  (h : History)
  (tx : Transaction)
  (h' : History)
  (hexec : TxExecRel ir h tx h') :
  h' = h ++ tx.writes := by
  exact hexec.1

end Cicsc.Core
