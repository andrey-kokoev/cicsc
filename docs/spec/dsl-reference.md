# CICSC Spec DSL Reference Manual

This manual provides a comprehensive reference for the CICSC Surface Language (Spec DSL), an ergonomic, indentation-aware language designed for describing socio-technical control systems.

## Core Concepts

The DSL centers on four primary constructs:
1. **Entities**: State-bearing objects with defined transitions (commands).
2. **Views**: Read-side projections of entity data.
3. **Constraints**: Invariants that must hold across all entities.
4. **Migrations**: Rules for evolving data between schema versions.

---

## Syntax Overview

### Indentation
CICSC uses Python-like mandatory indentation to define blocks. Each level of indentation must be consistent (4 spaces recommended).

### Keywords
- `entity`: Defines a new entity type.
- `command`: Defines an action that can be taken on an entity.
- `view`: Defines a queryable projection.
- `constraint`: Defines a global invariant.
- `attr`: Defines a persistent attribute on an entity.
- `shadow`: Defines a calculated field indexed for queries.

---

## Entity Declaration

Entities are the primary units of state.

```cicsc
entity Ticket:
    states: [Open, InProgress, Resolved, Closed]
    initial: Open

    attr title: string
    attr severity: int
    attr description: string optional

    shadow open_since: time
```

### State Management
- `states`: A list of allowed states.
- `initial`: The state an entity starts in. Defaults to the first state in the list if omitted.

### Attributes (`attr`)
Attributes are stored in the entity's `attrs` JSON blob.
Types: `string`, `int`, `float`, `bool`, `time`, `enum[...]`.
`optional`: Allows the attribute to be null.

### Shadow Columns (`shadow`)
Shadow columns are materialized into the database for performant querying and indexing. They are updated via reducers.

---

## Commands

Commands define how entities transition between states and how their data changes.

```cicsc
    command Resolve:
        input comment: string
        when state is InProgress
        auth actor.role is "Admin" or actor_id is row.assignee
        emit Resolved(comment: input.comment)
```

### Clauses
- `input`: Defines parameters for the command.
- `when`: Guard expression. The command fails if this is false.
- `auth`: Authorization logic.
- `emit`: Declares which events are produced. Events are processed by reducers to update state.

### Implicit Emit Sugar
If a command `X` has no `emit` clause, it implicitly emits an event `Xed` containing all command inputs.

---

## Views

Views provide a way to query the system state.

```cicsc
view OpenTickets:
    on Ticket
    where state is Open and severity > 5
    order_by severity desc
    limit 10
```

---

## Constraints

Constraints enforce invariants across the entire system.

```cicsc
constraint HighSeverityCapacity:
    on Ticket
    when state is Open
    assert count() < 100
```

---

## Predicate Sugar

The DSL supports natural language shortcuts for common expressions:
- `state is X` -> `state == "X"`
- `input.name is empty` -> `input.name == ""` or `input.name == null`
- `actor has role "Admin"` -> `actor.role == "Admin"`

---

## Type System

- `string`: UTF-8 string.
- `int`: 64-bit integer.
- `float`: 64-bit floating point.
- `bool`: true or false.
- `time`: Unix timestamp (seconds).
- `enum [A, B, C]`: A fixed set of string values.
