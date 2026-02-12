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

end Cicsc.Core
