import Cicsc.Core.Semantics.QueryEval
import Cicsc.Sql.Exec

namespace Cicsc.Sql
open Cicsc.Core

def rowSetEquiv (a b : List QueryRow) : Prop :=
  (∀ r, r ∈ a → r ∈ b) ∧ (∀ r, r ∈ b → r ∈ a)

def rowSeqEquiv (a b : List QueryRow) : Prop :=
  a = b

def rowsEquiv (ordered : Bool) (a b : List QueryRow) : Prop :=
  if ordered then rowSeqEquiv a b else rowSetEquiv a b

theorem rowSetEquiv_refl (rows : List QueryRow) : rowSetEquiv rows rows := by
  constructor <;> intro r hr <;> exact hr

theorem rowSetEquiv_symm (a b : List QueryRow) : rowSetEquiv a b → rowSetEquiv b a := by
  intro h
  exact ⟨h.2, h.1⟩

theorem rowSetEquiv_trans (a b c : List QueryRow) :
  rowSetEquiv a b → rowSetEquiv b c → rowSetEquiv a c := by
  intro hab hbc
  constructor
  · intro r hra
    exact hbc.1 r (hab.1 r hra)
  · intro r hrc
    exact hab.2 r (hbc.2 r hrc)

theorem rowsEquiv_unordered_refl (rows : List QueryRow) :
  rowsEquiv false rows rows := by
  unfold rowsEquiv
  simp [rowSetEquiv_refl]

theorem rowsEquiv_ordered_refl (rows : List QueryRow) :
  rowsEquiv true rows rows := by
  unfold rowsEquiv rowSeqEquiv
  simp

end Cicsc.Sql
