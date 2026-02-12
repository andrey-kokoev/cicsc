import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.Replay

namespace Cicsc.Examples
open Cicsc.Core

def ticketType : TypeSpec := {
  idType := "string"
  states := ["new", "done"]
  initialState := "new"
  attrs := []
  shadows := []
  commands := []
  reducer := [
    ("created", []),
    ("closed", [.setState (.litString "done")])
  ]
}

def ticketIr : IR := {
  version := 0
  types := [("Ticket", ticketType)]
}

def ticketHistory : History := [
  {
    tenantId := "t"
    entityType := "Ticket"
    entityId := "A"
    seq := 1
    eventType := "created"
    payload := .vObj []
    ts := 1
    actor := "u"
  },
  {
    tenantId := "t"
    entityType := "Ticket"
    entityId := "A"
    seq := 2
    eventType := "closed"
    payload := .vObj []
    ts := 2
    actor := "u"
  }
]

def ticketReplay : Option State := replay ticketIr "Ticket" ticketHistory

end Cicsc.Examples
