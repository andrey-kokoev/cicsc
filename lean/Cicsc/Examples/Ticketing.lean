import Cicsc.Core.Syntax
import Cicsc.Core.Types
import Cicsc.Core.Semantics.Replay
import Cicsc.Evolution.Migration
import Cicsc.Evolution.Naturality

namespace Cicsc.Examples
open Cicsc.Core
open Cicsc.Evolution

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

def ticketTypeV1 : TypeSpec := {
  idType := "string"
  states := ["open", "closed"]
  initialState := "open"
  attrs := []
  shadows := []
  commands := []
  reducer := [
    ("created", []),
    ("resolved", [.setState (.litString "closed")])
  ]
}

def ticketIrV1 : IR := {
  version := 1
  types := [("Ticket", ticketTypeV1)]
}

def ticketMigrationV0V1 : MigrationSpec := {
  fromVersion := 0
  toVersion := 1
  entityType := "Ticket"
  transforms := [
    { source := "created", target := "created", drop := false },
    { source := "closed", target := "resolved", drop := false }
  ]
  stateMap := [
    ("new", "open"),
    ("done", "closed")
  ]
}

def ticketInitialV0 : State := initialState ticketType

theorem ticket_v0_v1_non_identity_commutes_on_sample :
  Commutes ticketIr ticketIrV1 "Ticket" ticketMigrationV0V1 ticketInitialV0 ticketHistory := by
  decide

end Cicsc.Examples
