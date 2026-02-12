import Cicsc.Core.Syntax

namespace Cicsc.Core

inductive Ty where
  | tBool
  | tInt
  | tString
  | tNull
  | tObj
  | tArr
deriving Repr, DecidableEq

inductive Val where
  | vBool (b : Bool)
  | vInt (n : Int)
  | vString (s : String)
  | vNull
  | vObj (fields : List (String × Val))
  | vArr (items : List Val)
deriving Repr, DecidableEq

abbrev AttrMap := List (String × Val)
abbrev ShadowMap := List (String × Val)

structure EventCtx where
  eType : String
  eActor : String
  eTime : Nat
  ePayload : Val
deriving Repr, DecidableEq

structure Env where
  now : Nat
  actor : String
  state : String
  input : AttrMap := []
  attrs : AttrMap := []
  row : AttrMap := []
  arg : AttrMap := []
  rowsCount : Option Nat := none
  eventCtx : Option EventCtx := none
deriving Repr, DecidableEq

structure State where
  st : String
  attrs : AttrMap := []
  shadows : ShadowMap := []
deriving Repr, DecidableEq

structure Event where
  tenantId : String
  entityType : String
  entityId : String
  seq : Nat
  eventType : String
  payload : Val
  ts : Nat
  actor : String
deriving Repr, DecidableEq

abbrev History := List Event

structure StreamId where
  tenantId : String
  entityType : String
  entityId : String
deriving Repr, DecidableEq

def valTy : Val → Ty
  | .vBool _ => .tBool
  | .vInt _ => .tInt
  | .vString _ => .tString
  | .vNull => .tNull
  | .vObj _ => .tObj
  | .vArr _ => .tArr

end Cicsc.Core
