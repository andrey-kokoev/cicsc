import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.ExprEval

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

def applyOp (env : Env) (st : State) : ReducerOp → State
  | .setState expr =>
      match evalExpr env expr with
      | .vString s => { st with st := s }
      | _ => st
  | .setAttr name expr =>
      { st with attrs := setField st.attrs name (evalExpr env expr) }
  | .clearAttr name =>
      { st with attrs := clearField st.attrs name }
  | .setShadow name expr =>
      { st with shadows := setField st.shadows name (evalExpr env expr) }

def applyReducer (ts : TypeSpec) (st : State) (e : Event) : State :=
  let ops := lookupReducerOps ts e.eventType
  let env : Env := {
    now := e.ts
    actor := e.actor
    state := st.st
    attrs := st.attrs
    eventCtx := some {
      eType := e.eventType
      eActor := e.actor
      eTime := e.ts
      ePayload := e.payload
    }
  }
  ops.foldl (fun acc op => applyOp env acc op) st

def initialState (ts : TypeSpec) : State :=
  { st := ts.initialState, attrs := [], shadows := [] }

def replay (ir : IR) (typeName : String) (h : History) : Option State :=
  match lookupTypeSpec ir typeName with
  | none => none
  | some ts =>
      let stream := h.filter (fun e => e.entityType = typeName)
      some (stream.foldl (fun acc e => applyReducer ts acc e) (initialState ts))

end Cicsc.Core
