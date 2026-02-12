import Cicsc.Core.Meta.Typecheck
import Cicsc.Core.Semantics.Replay
import Cicsc.Core.Semantics.Commands
import Cicsc.Core.Semantics.Constraints
import Cicsc.Core.Semantics.QueryEval

namespace Cicsc.Core

def RuntimeStateProjection (env : Env) (st : State) : Prop :=
  env.state = st.st ∧ env.attrs = st.attrs ∧ env.row = mkRow st

theorem reducerEnv_runtimeProjection
  (st : State) (e : Event) :
  RuntimeStateProjection (reducerEnv st e) st := by
  simpa [RuntimeStateProjection] using reducerEnv_usesStateRowAttrs st e

theorem commandEnv_runtimeProjection
  (st : State) (env : Env) :
  RuntimeStateProjection (commandEnv st env) st := by
  simpa [RuntimeStateProjection] using commandEnv_usesStateRowAttrs st env

theorem snapshotEnv_runtimeProjection
  (st : State) :
  RuntimeStateProjection (snapshotEnv st) st := by
  simpa [RuntimeStateProjection] using snapshotEnv_usesStateRowAttrs st

theorem commandTypeEnv_decomposes
  (ts : TypeSpec)
  (cmd : CommandSpec)
  (Γ : TypeEnv)
  (h : commandTypeEnv ts cmd = some Γ) :
  ∃ Γstate Γinput,
    stateTypeEnv ts = some Γstate ∧
    mkInputEnv cmd.input = some Γinput ∧
    Γ = Γinput ++ Γstate := by
  unfold commandTypeEnv at h
  cases hState : stateTypeEnv ts <;> simp [hState] at h
  cases hInput : mkInputEnv cmd.input <;> simp [hInput] at h
  cases h
  exact ⟨_, _, hState, hInput, rfl⟩

theorem rowEnv_runtimeProjection
  (row : QueryRow) :
  (rowEnv row).row = row ∧ (rowEnv row).state = rowStateValue row := by
  simpa using rowEnv_usesRowAndState row

end Cicsc.Core
