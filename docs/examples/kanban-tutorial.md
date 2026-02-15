# Tutorial: Kanban Board with Constraints

This tutorial shows how to use global constraints to enforce "Work in Progress" (WIP) limits.

## The Spec

```cicsc
entity Card:
    states: [Todo, Doing, Done]
    attr title: string

constraint WIPLimit:
    on Card
    when state is Doing
    assert count() <= 5
```

## How it works

1. When a user tries to move a 6th card into the `Doing` state (via a command), the **Constraint Engine** runs.
2. It detects that the invariant `count() <= 5` would be violated by this transition.
3. The entire transaction is rolled back.
4. The user receives a clear error: `Constraint HighSeverityCapacity rejected the transition`.

## Querying the Board

Views can reflect the board layout:

```cicsc
view DoingBoard:
    on Card
    where state is Doing
    order_by updated_ts asc
```
