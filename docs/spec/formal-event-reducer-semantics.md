# Formal Semantics: Event Algebra and Reducer Fold

Let an event stream be:

`E = [e1, e2, ..., en]`

where each event `ei` is ordered by `(tenant, type, entity, seq)`.

Let `S0(T)` be initial snapshot for entity type `T`.

Define reducer step:

`step : Snapshot x Event -> Snapshot`

where `step(s, e)` applies reducer ops keyed by `e.event_type`.

Define replay fold:

`Replay_T(E) = foldl(step, S0(T), E)`

Properties:

1. Determinism: `Replay_T(E)` is unique for fixed `E` and deterministic intrinsics.
2. Prefix monotonicity: replay over prefix `E_k` yields intermediate state at seq `k`.
3. Totality requirement: reducer must exist for every emitted event type.

Operationally, committed snapshot state must equal replay fold over committed history.
