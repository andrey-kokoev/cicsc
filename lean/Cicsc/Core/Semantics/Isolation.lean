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

theorem snapshot_no_dirty_reads
  (sid : StreamId)
  (beginSeq : Nat)
  (e : Event)
  (hvis : visibleAtSeq sid beginSeq e = true) :
  e.seq ≤ beginSeq := by
  unfold visibleAtSeq at hvis
  simp at hvis
  exact hvis.2

theorem snapshot_repeatable_reads
  (ir : IR)
  (h : History)
  (tx1 tx2 : Transaction)
  (hiso1 : tx1.isolation = .snapshot)
  (hiso2 : tx2.isolation = .snapshot)
  (hsid : tx1.sid = tx2.sid)
  (hbegin : tx1.beginSeq = tx2.beginSeq) :
  readSnapshot ir h tx1 = readSnapshot ir h tx2 := by
  unfold readSnapshot snapshotAt readCutoff
  simp [hiso1, hiso2, hsid, hbegin]

end Cicsc.Core
