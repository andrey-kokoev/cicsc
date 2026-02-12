import Lean
import Cicsc.Core.Meta.WF

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

elab "wf_auto" : tactic => do
  evalTactic (← `(tactic|
    (first
      | exact Cicsc.Core.wfIR_of_checkIR _ ‹Cicsc.Core.checkIR _ = true›
      | exact Cicsc.Core.wfTypeSpec_of_checkTypeSpec _ ‹Cicsc.Core.checkTypeSpec _ = true›
      | simp at *)))

end Cicsc.Tactics
