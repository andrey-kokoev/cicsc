import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.ExprEval
import Cicsc.Core.Semantics.Replay

namespace Cicsc.Core

structure EmittedEvent where
  tenantId : String
  entityType : String
  entityId : String
  eventType : String
  payload : Val
  ts : Nat
  actor : String
deriving Repr, DecidableEq

def lookupCommand (ts : TypeSpec) (name : String) : Option CommandSpec :=
  match ts.commands.find? (fun (kv) => kv.fst = name) with
  | some kv => some kv.snd
  | none => none

def materializePayload (env : Env) (pairs : List (String × Expr)) : List (String × Val) :=
  pairs.map (fun kv => (kv.fst, evalExpr env kv.snd))

def materializeEvents (env : Env) (es : List (EventType × List (String × Expr))) : List (EventType × Val) :=
  es.map (fun e => (e.fst, .vObj (materializePayload env e.snd)))

def commandEnv (st : State) (env : Env) : Env :=
  { env with
    state := st.st
    attrs := st.attrs
    row := mkRow st
  }

theorem commandEnv_usesStateRowAttrs
  (st : State)
  (env : Env) :
  (commandEnv st env).state = st.st ∧
  (commandEnv st env).attrs = st.attrs ∧
  (commandEnv st env).row = mkRow st := by
  simp [commandEnv]

def canExecute (cmd : CommandSpec) (envExec : Env) : Bool :=
  toBool (evalExpr envExec cmd.guard)

def executeCommand (ts : TypeSpec) (sid : StreamId) (cmdName : String) (st : State) (env : Env) :
  Option (List EmittedEvent) :=
  match lookupCommand ts cmdName with
  | none => none
  | some cmd =>
      let envExec := commandEnv st env
      if !canExecute cmd envExec then none
      else
        let es := materializeEvents envExec cmd.emits
        let emitted : List EmittedEvent :=
          es.map (fun e => {
            tenantId := sid.tenantId
            entityType := sid.entityType
            entityId := sid.entityId
            eventType := e.fst
            payload := e.snd
            ts := env.now
            actor := env.actor
          })
        some emitted

def applyEmittedEvents (ts : TypeSpec) (st : State) (es : List EmittedEvent) : State :=
  es.foldl
    (fun acc e =>
      applyReducer ts acc {
        tenantId := e.tenantId
        entityType := e.entityType
        entityId := e.entityId
        -- Local projection only; persistent sequence assignment belongs to runtime storage.
        seq := 0
        eventType := e.eventType
        payload := e.payload
        ts := e.ts
        actor := e.actor
      })
    st

end Cicsc.Core
