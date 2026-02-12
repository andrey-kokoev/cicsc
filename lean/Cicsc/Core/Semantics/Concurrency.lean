import Cicsc.Core.Types

namespace Cicsc.Core

def sameStream (e1 e2 : Event) : Prop :=
  e1.tenantId = e2.tenantId ∧
  e1.entityType = e2.entityType ∧
  e1.entityId = e2.entityId

def happensBefore (e1 e2 : Event) : Prop :=
  sameStream e1 e2 ∧ e1.seq < e2.seq

theorem happensBefore_irrefl (e : Event) : ¬ happensBefore e e := by
  intro h
  exact Nat.lt_irrefl e.seq h.2

theorem sameStream_refl (e : Event) : sameStream e e := by
  simp [sameStream]

theorem sameStream_symm (e1 e2 : Event) : sameStream e1 e2 → sameStream e2 e1 := by
  intro h
  rcases h with ⟨h1, h2, h3⟩
  exact ⟨h1.symm, h2.symm, h3.symm⟩

theorem sameStream_trans (e1 e2 e3 : Event) :
  sameStream e1 e2 → sameStream e2 e3 → sameStream e1 e3 := by
  intro h12 h23
  rcases h12 with ⟨h12a, h12b, h12c⟩
  rcases h23 with ⟨h23a, h23b, h23c⟩
  exact ⟨h12a.trans h23a, h12b.trans h23b, h12c.trans h23c⟩

theorem happensBefore_trans (e1 e2 e3 : Event) :
  happensBefore e1 e2 → happensBefore e2 e3 → happensBefore e1 e3 := by
  intro h12 h23
  refine ⟨sameStream_trans e1 e2 e3 h12.1 h23.1, Nat.lt_trans h12.2 h23.2⟩

theorem happensBefore_asymm (e1 e2 : Event) :
  happensBefore e1 e2 → ¬ happensBefore e2 e1 := by
  intro h12 h21
  exact Nat.lt_asymm h12.2 h21.2

def appearsBefore (h : History) (e1 e2 : Event) : Prop :=
  ∃ pre mid post, h = pre ++ (e1 :: mid ++ e2 :: post)

def isCausal (h : History) : Prop :=
  ∀ e1 e2, e1 ∈ h → e2 ∈ h → happensBefore e1 e2 → appearsBefore h e1 e2

end Cicsc.Core
