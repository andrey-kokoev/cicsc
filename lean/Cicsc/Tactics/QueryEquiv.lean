import Lean

open Lean Elab Tactic

namespace Cicsc.Tactics

elab "query_equiv" : tactic => do
  evalTactic (← `(tactic|
    (unfold Cicsc.Sql.rowsEquiv Cicsc.Sql.rowSetEquiv Cicsc.Sql.rowSeqEquiv
     <;> simp)))

end Cicsc.Tactics
