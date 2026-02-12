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

def canExecute (cmd : CommandSpec) (env : Env) : Bool :=
  toBool (evalExpr env cmd.guard)

def executeCommand (ts : TypeSpec) (cmdName : String) (st : State) (env : Env) : Option State :=
  match lookupCommand ts cmdName with
  | none => none
  | some cmd =>
      if !canExecute cmd env then none
      else
        let es := materializeEvents env cmd.emits
        let fakeHistory : History :=
          es.enum.map (fun (ix, e) => {
            tenantId := ""
            entityType := ""
            entityId := ""
            seq := ix.succ
            eventType := e.fst
            payload := e.snd
            ts := env.now
            actor := env.actor
          })
        let out := fakeHistory.foldl (fun acc e => applyReducer ts acc e) st
        some out

end Cicsc.Core
