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

theorem appearsBefore_filter_preserved
  (p : Event → Bool)
  (h : History)
  (e1 e2 : Event)
  (hbefore : appearsBefore h e1 e2)
  (h1 : p e1 = true)
  (h2 : p e2 = true) :
  appearsBefore (h.filter p) e1 e2 := by
  rcases hbefore with ⟨pre, mid, post, hdecomp⟩
  subst hdecomp
  refine ⟨pre.filter p, mid.filter p, post.filter p, ?_⟩
  simp [List.filter_append, h1, h2, List.append_assoc]

theorem replay_stream_preserves_happensBefore_order
  (h : History)
  (sid : StreamId)
  (hcausal : isCausal h)
  (e1 e2 : Event)
  (he1 : e1 ∈ h.filter (inStream sid))
  (he2 : e2 ∈ h.filter (inStream sid))
  (hbefore : happensBefore e1 e2) :
  appearsBefore (h.filter (inStream sid)) e1 e2 := by
  have hInOriginal : appearsBefore h e1 e2 :=
    replay_stream_events_respect_causal_order h sid hcausal e1 e2 he1 he2 hbefore
  have hin1 : inStream sid e1 = true := ((mem_streamFilter_iff sid h e1).1 he1).2
  have hin2 : inStream sid e2 = true := ((mem_streamFilter_iff sid h e2).1 he2).2
  exact appearsBefore_filter_preserved (inStream sid) h e1 e2 hInOriginal hin1 hin2

def concurrent (e1 e2 : Event) : Prop :=
  sameStream e1 e2 ∧ ¬ happensBefore e1 e2 ∧ ¬ happensBefore e2 e1

def CommutesOnConcurrent (ts : TypeSpec) : Prop :=
  ∀ (st : State) (e1 e2 : Event),
    concurrent e1 e2 →
      applyReducer ts (applyReducer ts st e1) e2 =
      applyReducer ts (applyReducer ts st e2) e1

theorem concurrent_symm (e1 e2 : Event) :
  concurrent e1 e2 → concurrent e2 e1 := by
  intro h
  rcases h with ⟨hss, h12, h21⟩
  exact ⟨sameStream_symm e1 e2 hss, h21, h12⟩

theorem replayFold_swap_adjacent_concurrent
  (ts : TypeSpec)
  (st : State)
  (pre post : List Event)
  (e1 e2 : Event)
  (hconc : concurrent e1 e2)
  (hcomm : CommutesOnConcurrent ts) :
  (pre ++ e1 :: e2 :: post).foldl (fun acc e => applyReducer ts acc e) st =
    (pre ++ e2 :: e1 :: post).foldl (fun acc e => applyReducer ts acc e) st := by
  let st0 := pre.foldl (fun acc e => applyReducer ts acc e) st
  have hswap :
      applyReducer ts (applyReducer ts st0 e1) e2 =
        applyReducer ts (applyReducer ts st0 e2) e1 := by
    exact hcomm st0 e1 e2 hconc
  simp [List.foldl_append, st0, hswap]

inductive CausallyEquivalent : History → History → Prop where
  | refl (h : History) : CausallyEquivalent h h
  | swap (pre post : List Event) (e1 e2 : Event) :
      concurrent e1 e2 →
      CausallyEquivalent (pre ++ e1 :: e2 :: post) (pre ++ e2 :: e1 :: post)
  | trans {h1 h2 h3 : History} :
      CausallyEquivalent h1 h2 →
      CausallyEquivalent h2 h3 →
      CausallyEquivalent h1 h3

theorem replayFold_causallyEquivalent
  (ts : TypeSpec)
  (st : State)
  (h1 h2 : History)
  (hce : CausallyEquivalent h1 h2)
  (hcomm : CommutesOnConcurrent ts) :
  h1.foldl (fun acc e => applyReducer ts acc e) st =
    h2.foldl (fun acc e => applyReducer ts acc e) st := by
  induction hce with
  | refl h =>
      rfl
  | swap pre post e1 e2 hconc =>
      simpa using replayFold_swap_adjacent_concurrent ts st pre post e1 e2 hconc hcomm
  | trans h12 h23 ih12 ih23 =>
      exact ih12.trans ih23

theorem replay_deterministic_on_causallyEquivalent_streams
  (ir : IR)
  (sid : StreamId)
  (h1 h2 : History)
  (ts : TypeSpec)
  (hlookup : lookupTypeSpec ir sid.entityType = some ts)
  (hce : CausallyEquivalent (h1.filter (inStream sid)) (h2.filter (inStream sid)))
  (hcomm : CommutesOnConcurrent ts) :
  replay ir sid h1 = replay ir sid h2 := by
  unfold replay
  simp [hlookup]
  exact replayFold_causallyEquivalent ts (initialState ts)
    (h1.filter (inStream sid))
    (h2.filter (inStream sid))
    hce
    hcomm

end Cicsc.Core
