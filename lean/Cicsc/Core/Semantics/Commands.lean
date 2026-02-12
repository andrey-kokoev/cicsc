import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.ExprEval
import Cicsc.Core.Semantics.Replay

namespace Cicsc.Core

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
    row := runtimeRow st
  }

def canExecute (cmd : CommandSpec) (envExec : Env) : Bool :=
  toBool (evalExpr envExec cmd.guard)

def executeCommand (ts : TypeSpec) (sid : StreamId) (cmdName : String) (st : State) (env : Env) : Option State :=
  match lookupCommand ts cmdName with
  | none => none
  | some cmd =>
      let envExec := commandEnv st env
      if !canExecute cmd envExec then none
      else
        let es := materializeEvents envExec cmd.emits
        let emittedHistory : History :=
          es.enum.map (fun (ix, e) => {
            tenantId := sid.tenantId
            entityType := sid.entityType
            entityId := sid.entityId
            seq := ix.succ
            eventType := e.fst
            payload := e.snd
            ts := env.now
            actor := env.actor
          })
        let out := emittedHistory.foldl (fun acc e => applyReducer ts acc e) st
        some out

end Cicsc.Core
