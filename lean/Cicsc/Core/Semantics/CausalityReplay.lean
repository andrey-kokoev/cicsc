import Cicsc.Core.Semantics.Concurrency
import Cicsc.Core.Semantics.Replay

namespace Cicsc.Core

theorem mem_streamFilter_iff
  (sid : StreamId)
  (h : History)
  (e : Event) :
  e ∈ h.filter (inStream sid) ↔ e ∈ h ∧ inStream sid e = true := by
  simp [List.mem_filter]

theorem sameStream_of_inStream_true
  (sid : StreamId)
  (e : Event)
  (hin : inStream sid e = true) :
  sameStream e {
    tenantId := sid.tenantId
    entityType := sid.entityType
    entityId := sid.entityId
    seq := e.seq
    eventType := e.eventType
    payload := e.payload
    ts := e.ts
    actor := e.actor
  } := by
  unfold sameStream inStream at *
  simp at hin
  rcases hin with ⟨ht, hty, hid⟩
  constructor
  · exact ht
  constructor
  · exact hty
  · exact hid

theorem sameStream_of_inStream_true_true
  (sid : StreamId)
  (e1 e2 : Event)
  (h1 : inStream sid e1 = true)
  (h2 : inStream sid e2 = true) :
  sameStream e1 e2 := by
  unfold sameStream inStream at *
  simp at h1 h2
  rcases h1 with ⟨ht1, hty1, hid1⟩
  rcases h2 with ⟨ht2, hty2, hid2⟩
  constructor
  · exact ht1.trans ht2.symm
  constructor
  · exact hty1.trans hty2.symm
  · exact hid1.trans hid2.symm

theorem isCausal_implies_appearsBefore_in_replayStream
  (h : History)
  (sid : StreamId)
  (hcausal : isCausal h)
  (e1 e2 : Event)
  (he1 : e1 ∈ h.filter (inStream sid))
  (he2 : e2 ∈ h.filter (inStream sid))
  (hseq : e1.seq < e2.seq) :
  appearsBefore h e1 e2 := by
  have he1h : e1 ∈ h := (mem_streamFilter_iff sid h e1).1 he1 |>.1
  have he2h : e2 ∈ h := (mem_streamFilter_iff sid h e2).1 he2 |>.1
  have hin1 : inStream sid e1 = true := (mem_streamFilter_iff sid h e1).1 he1 |>.2
  have hin2 : inStream sid e2 = true := (mem_streamFilter_iff sid h e2).1 he2 |>.2
  have hss : sameStream e1 e2 := sameStream_of_inStream_true_true sid e1 e2 hin1 hin2
  exact hcausal e1 e2 he1h he2h ⟨hss, hseq⟩

theorem replay_stream_events_respect_causal_order
  (h : History)
  (sid : StreamId)
  (hcausal : isCausal h)
  (e1 e2 : Event)
  (he1 : e1 ∈ h.filter (inStream sid))
  (he2 : e2 ∈ h.filter (inStream sid))
  (hbefore : happensBefore e1 e2) :
  appearsBefore h e1 e2 := by
  exact hcausal e1 e2
    ((mem_streamFilter_iff sid h e1).1 he1).1
    ((mem_streamFilter_iff sid h e2).1 he2).1
    hbefore

end Cicsc.Core
