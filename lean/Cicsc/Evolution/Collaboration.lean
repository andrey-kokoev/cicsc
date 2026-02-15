namespace Cicsc.Evolution.Collaboration

/-- Collaboration message status -/
inductive MessageStatus
  | sent
  | inProgress
  | fulfilled
  | closed
  | ingested
  | rescinded
  deriving DecidableEq, Repr

/-- Message event transitions -/
inductive CollabEvent
  | send
  | claim
  | complete
  | close
  | ingest
  | rescind
  deriving DecidableEq, Repr

/-- Collaboration state machine transition function -/
def nextStatus (current : Option MessageStatus) (event : CollabEvent) : Option MessageStatus :=
  match current, event with
  | none,            CollabEvent.send     => some MessageStatus.sent
  | some MessageStatus.sent,       CollabEvent.claim    => some MessageStatus.inProgress
  | some MessageStatus.inProgress, CollabEvent.complete => some MessageStatus.fulfilled
  | some MessageStatus.fulfilled,  CollabEvent.close    => some MessageStatus.closed
  | some MessageStatus.closed,     CollabEvent.ingest   => some MessageStatus.ingested
  | some MessageStatus.sent,       CollabEvent.rescind  => some MessageStatus.rescinded
  | some MessageStatus.inProgress, CollabEvent.rescind  => some MessageStatus.rescinded
  | _, _ => none -- Illegal transition

/-- Event with sequence number and message ID -/
structure EventEnvelope where
  msgId : String
  seq   : Nat
  event : CollabEvent

/-- Fold a sequence of events for a specific message -/
def foldMessageStatus (events : List EventEnvelope) : Option MessageStatus :=
  events.foldl (fun status env =>
    match nextStatus status env.event with
    | some s => some s
    | none   => status -- In a real system we might error, but standard fold persists last valid
  ) none

/-- Legal transition property: status only moves forward according to state machine -/
def LegalTransition (s1 s2 : MessageStatus) : Prop :=
  ∃ e, nextStatus (some s1) e = some s2

/-- Safety: no sent -> fulfilled skip -/
theorem no_sent_fulfilled_skip (e : CollabEvent) :
  nextStatus (some MessageStatus.sent) e = some MessageStatus.fulfilled → False := by
  cases e <;> simp [nextStatus]

/-- Safety: fulfilled is only reachable from inProgress -/
theorem fulfilled_from_inProgress (s : MessageStatus) (e : CollabEvent) :
  nextStatus (some s) e = some MessageStatus.fulfilled → s = MessageStatus.inProgress := by
  intro h
  cases s <;> cases e <;> simp [nextStatus] at h <;> (try contradiction)
  rfl

/-- Sequence monotonicity: events for same message must have increasing seq -/
def MonotonicEvents (events : List EventEnvelope) : Prop :=
  match events with
  | [] => True
  | [_] => True
  | e1 :: e2 :: rest => e1.seq < e2.seq ∧ MonotonicEvents (e2 :: rest)

/-- BA2.1: Close preconditions -/
def CanClose (s : MessageStatus) : Prop :=
  s = MessageStatus.fulfilled ∨ s = MessageStatus.ingested

theorem close_requires_precondition (s : MessageStatus) :
  nextStatus (some s) CollabEvent.close = some MessageStatus.closed → CanClose s := by
  cases s <;> simp [nextStatus, CanClose]

/-- BA2.2: Post-close terminality (once closed, it stays closed or moved to ingested) -/
theorem closed_to_ingested_monotone (s : MessageStatus) (e : CollabEvent) :
  nextStatus (some MessageStatus.closed) e = some s → s = MessageStatus.ingested := by
  intro h
  cases e <;> simp [nextStatus] at h <;> (try contradiction)
  exact h.symm

/-- BA2.3: Rescind admissibility -/
def CanRescind (s : MessageStatus) : Prop :=
  s = MessageStatus.sent ∨ s = MessageStatus.inProgress

theorem rescind_admissibility (s : MessageStatus) :
  nextStatus (some s) CollabEvent.rescind = some MessageStatus.rescinded → CanRescind s := by
  intro h
  cases s <;> simp [nextStatus] at h <;> (try contradiction)
  case sent => exact Or.inl rfl
  case inProgress => exact Or.inr rfl

/-- Non-interference: rescinded cannot be fulfilled or closed -/
theorem rescinded_is_terminal (s : MessageStatus) (e : CollabEvent) :
  nextStatus (some MessageStatus.rescinded) e = some s → False := by
  intro h
  cases e <;> simp [nextStatus] at h

end Cicsc.Evolution.Collaboration
