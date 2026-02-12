import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.Replay

namespace Cicsc.Examples
open Cicsc.Core

def cardType : TypeSpec := {
  idType := "string"
  states := ["backlog", "in_progress", "done"]
  initialState := "backlog"
  attrs := [("title", "string")]
  shadows := []
  commands := []
  reducer := [
    ("created", []),
    ("started", [.setState (.litString "in_progress")]),
    ("completed", [.setState (.litString "done")])
  ]
}

def kanbanIr : IR := {
  version := 0
  types := [("Card", cardType)]
}

def kanbanHistory : History := [
  {
    tenantId := "t"
    entityType := "Card"
    entityId := "C1"
    seq := 1
    eventType := "created"
    payload := .vObj [("title", .vString "build lean model")]
    ts := 1
    actor := "u"
  },
  {
    tenantId := "t"
    entityType := "Card"
    entityId := "C1"
    seq := 2
    eventType := "started"
    payload := .vObj []
    ts := 2
    actor := "u"
  },
  {
    tenantId := "t"
    entityType := "Card"
    entityId := "C1"
    seq := 3
    eventType := "completed"
    payload := .vObj []
    ts := 3
    actor := "u"
  }
]

def kanbanStream : StreamId := {
  tenantId := "t"
  entityType := "Card"
  entityId := "C1"
}

def kanbanReplay : Option State := replay kanbanIr kanbanStream kanbanHistory

end Cicsc.Examples
