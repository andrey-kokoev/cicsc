import Lean

open Lean Elab Tactic

namespace Cicsc.Tactics

elab "query_equiv" : tactic => do
  evalTactic (← `(tactic|
    (unfold Cicsc.Sql.rowsEquiv Cicsc.Sql.rowSetEquiv Cicsc.Sql.rowSeqEquiv
     <;> simp)))

elab "snap_irrelevant" : tactic => do
  evalTactic (← `(tactic|
    (simp [List.mem_filter, Cicsc.Core.lookupSnapRows, Cicsc.Core.visibleAtSeq,
      Bool.and_eq_true] at *)))

end Cicsc.Tactics
