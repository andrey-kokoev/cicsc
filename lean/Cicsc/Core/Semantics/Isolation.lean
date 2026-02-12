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

def writeWriteConflict (tx1 tx2 : Transaction) : Prop :=
  tx1.sid = tx2.sid ∧ tx1.beginSeq < tx2.commitSeq ∧ tx2.beginSeq < tx1.commitSeq

inductive TxConflictOutcome where
  | abort
  | serialize
deriving Repr, DecidableEq

def resolveWriteWriteConflict (tx1 tx2 : Transaction) : TxConflictOutcome :=
  if writeWriteConflict tx1 tx2 then .abort else .serialize

theorem writeWrite_conflict_abort_or_serialize
  (tx1 tx2 : Transaction)
  (hconflict : writeWriteConflict tx1 tx2) :
  resolveWriteWriteConflict tx1 tx2 = .abort ∨
    resolveWriteWriteConflict tx1 tx2 = .serialize := by
  unfold resolveWriteWriteConflict
  simp [hconflict]

theorem inStream_false_of_sid_ne
  (sid1 sid2 : StreamId)
  (hsid : sid1 ≠ sid2)
  (e : Event)
  (hin2 : inStream sid2 e = true) :
  inStream sid1 e = false := by
  unfold inStream at *
  simp at hin2
  rcases hin2 with ⟨ht2, hty2, hid2⟩
  by_cases h1 : sid1.tenantId = sid2.tenantId
  · by_cases h2 : sid1.entityType = sid2.entityType
    · by_cases h3 : sid1.entityId = sid2.entityId
      · exfalso
        apply hsid
        cases sid1
        cases sid2
        simp at *
        simp [h1, h2, h3]
      · simp [h1, h2, h3, ht2, hty2, hid2]
    · simp [h1, h2, ht2, hty2, hid2]
  · simp [h1, ht2, hty2, hid2]

theorem snapshotAt_ignores_other_stream_writes
  (ir : IR)
  (sidRead sidWrite : StreamId)
  (h : History)
  (writes : History)
  (cutoffSeq : Nat)
  (hsid : sidRead ≠ sidWrite)
  (hwrites : ∀ e ∈ writes, inStream sidWrite e = true) :
  snapshotAt ir sidRead (h ++ writes) cutoffSeq = snapshotAt ir sidRead h cutoffSeq := by
  unfold snapshotAt
  simp [List.filter_append]
  suffices hdrop : (writes.filter (visibleAtSeq sidRead cutoffSeq)) = [] by
    simp [hdrop]
  apply List.eq_nil_iff_forall_not_mem.2
  intro e he
  have hInFiltered : e ∈ writes.filter (visibleAtSeq sidRead cutoffSeq) := he
  have heInWrites : e ∈ writes := by
    exact (List.mem_filter.1 hInFiltered).1
  have hVis : visibleAtSeq sidRead cutoffSeq e = true := by
    exact (List.mem_filter.1 hInFiltered).2
  have hInWriteStream : inStream sidWrite e = true := hwrites e heInWrites
  have hInReadStreamFalse : inStream sidRead e = false :=
    inStream_false_of_sid_ne sidRead sidWrite hsid e hInWriteStream
  unfold visibleAtSeq in hVis
  simp [hInReadStreamFalse] at hVis

end Cicsc.Core
