import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.ExprEval
import Cicsc.Core.Semantics.Common
import Cicsc.Core.Meta.WF

namespace Cicsc.Core

def lookupTypeSpec (ir : IR) (typeName : String) : Option TypeSpec :=
  match ir.types.find? (fun (kv) => kv.fst = typeName) with
  | some kv => some kv.snd
  | none => none

def lookupReducerOps (ts : TypeSpec) (eventType : String) : List ReducerOp :=
  match ts.reducer.find? (fun (kv) => kv.fst = eventType) with
  | some kv => kv.snd
  | none => []

def setField (xs : List (String × Val)) (k : String) (v : Val) : List (String × Val) :=
  let rest := xs.filter (fun kv => kv.fst ≠ k)
  (k, v) :: rest

def clearField (xs : List (String × Val)) (k : String) : List (String × Val) :=
  xs.filter (fun kv => kv.fst ≠ k)

def applyOp (ts : TypeSpec) (env : Env) (st : State) : ReducerOp → State
  | .setState expr =>
      match evalExpr env expr with
      | .vString s =>
          if ts.states.contains s then { st with st := s } else st
      | _ => st
  | .setAttr name expr =>
      { st with attrs := setField st.attrs name (evalExpr env expr) }
  | .clearAttr name =>
      { st with attrs := clearField st.attrs name }
  | .setShadow name expr =>
      { st with shadows := setField st.shadows name (evalExpr env expr) }

def reducerEnv (st : State) (e : Event) : Env := {
  now := e.ts
  actor := e.actor
  state := st.st
  attrs := st.attrs
  row := mkRow st
  eventCtx := some {
    eType := e.eventType
    eActor := e.actor
    eTime := e.ts
    ePayload := e.payload
  }
}

def applyReducer (ts : TypeSpec) (st : State) (e : Event) : State :=
  let ops := lookupReducerOps ts e.eventType
  let env := reducerEnv st e
  ops.foldl (fun acc op => applyOp ts env acc op) st

theorem reducerEnv_usesStateRowAttrs
  (st : State)
  (e : Event) :
  (reducerEnv st e).state = st.st ∧
  (reducerEnv st e).attrs = st.attrs ∧
  (reducerEnv st e).row = mkRow st := by
  simp [reducerEnv]

def initialState (ts : TypeSpec) : State :=
  { st := ts.initialState, attrs := [], shadows := [] }

def inStream (sid : StreamId) (e : Event) : Bool :=
  e.tenantId = sid.tenantId && e.entityType = sid.entityType && e.entityId = sid.entityId

def replay (ir : IR) (sid : StreamId) (h : History) : Option State :=
  match lookupTypeSpec ir sid.entityType with
  | none => none
  | some ts =>
      let stream := h.filter (inStream sid)
      some (stream.foldl (fun acc e => applyReducer ts acc e) (initialState ts))

def WellFormedState (ts : TypeSpec) (st : State) : Prop :=
  st.st ∈ ts.states

def ReducerPreservesWF (ts : TypeSpec) : Prop :=
  ∀ (st : State) (e : Event), WellFormedState ts st → WellFormedState ts (applyReducer ts st e)

theorem applyOpPreservesWellFormed
  (ts : TypeSpec)
  (env : Env)
  (st : State)
  (op : ReducerOp)
  (hwf : WellFormedState ts st) :
  WellFormedState ts (applyOp ts env st op) := by
  cases op with
  | setState expr =>
      simp [applyOp, WellFormedState] at *
      cases hEval : evalExpr env expr <;> simp [hEval, hwf]
  | setAttr name expr =>
      simpa [applyOp] using hwf
  | clearAttr name =>
      simpa [applyOp] using hwf
  | setShadow name expr =>
      simpa [applyOp] using hwf

theorem foldOpsPreservesWellFormed
  (ts : TypeSpec)
  (env : Env) :
  ∀ (ops : List ReducerOp) (st : State),
    WellFormedState ts st →
    WellFormedState ts (ops.foldl (fun acc op => applyOp ts env acc op) st) := by
  intro ops
  induction ops with
  | nil =>
      intro st hwf
      simpa using hwf
  | cons op ops ih =>
      intro st hwf
      have hwf' : WellFormedState ts (applyOp ts env st op) :=
        applyOpPreservesWellFormed ts env st op hwf
      simpa using ih (applyOp ts env st op) hwf'

theorem reducerPreservesWF_of_runtimeStepGuard
  (ts : TypeSpec) :
  ReducerPreservesWF ts := by
  intro st e hwf
  unfold applyReducer
  exact foldOpsPreservesWellFormed ts (reducerEnv st e) (lookupReducerOps ts e.eventType) st hwf

theorem reducerPreservesWF_of_WFTypeSpec
  (ts : TypeSpec)
  (_hWf : WFTypeSpec ts) :
  ReducerPreservesWF ts := by
  exact reducerPreservesWF_of_runtimeStepGuard ts

theorem replayTotalIfTypeExists
  (ir : IR) (sid : StreamId) (h : History)
  (hex : ∃ ts, lookupTypeSpec ir sid.entityType = some ts) :
  ∃ st, replay ir sid h = some st := by
  rcases hex with ⟨ts, hts⟩
  unfold replay
  simp [lookupTypeSpec, hts]

theorem applyReducerPreservesWellFormed
  (ts : TypeSpec)
  (hpres : ReducerPreservesWF ts)
  (st : State)
  (e : Event)
  (hwf : WellFormedState ts st) :
  WellFormedState ts (applyReducer ts st e) := by
  exact hpres st e hwf

theorem replayDeterministic (ir : IR) (sid : StreamId) (h : History) :
  ∀ s1 s2, replay ir sid h = some s1 → replay ir sid h = some s2 → s1 = s2 := by
  intro s1 s2 h1 h2
  simpa [h1] using h2

theorem initialStateWellFormedOfWFTypeSpec
  (ts : TypeSpec)
  (hWf : WFTypeSpec ts) :
  WellFormedState ts (initialState ts) := by
  exact hWf.1

theorem replayFoldPreservesWellFormed
  (ts : TypeSpec)
  (hpres : ReducerPreservesWF ts) :
  ∀ (events : List Event) (st : State),
    WellFormedState ts st →
    WellFormedState ts (events.foldl (fun acc e => applyReducer ts acc e) st) := by
  intro events
  induction events with
  | nil =>
      intro st hwf
      simpa using hwf
  | cons e es ih =>
      intro st hwf
      have hwf' : WellFormedState ts (applyReducer ts st e) := hpres st e hwf
      simpa using ih (applyReducer ts st e) hwf'

theorem replayPreservesWellFormedIfTypeExists
  (ir : IR)
  (sid : StreamId)
  (h : History)
  (ts : TypeSpec)
  (hlookup : lookupTypeSpec ir sid.entityType = some ts)
  (hpres : ReducerPreservesWF ts)
  (hinit : WellFormedState ts (initialState ts)) :
  ∃ st, replay ir sid h = some st ∧ WellFormedState ts st := by
  unfold replay
  simp [hlookup]
  let stream := h.filter (inStream sid)
  refine ⟨stream.foldl (fun acc e => applyReducer ts acc e) (initialState ts), ?_⟩
  constructor
  · rfl
  · exact replayFoldPreservesWellFormed ts hpres stream (initialState ts) hinit

end Cicsc.Core
