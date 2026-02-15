# Tutorial: Building a Ticketing System

This tutorial walks you through creating a simple ticketing system from scratch using CICSC.

## 1. Define the Spec

Create a file named `ticketing.cicsc`:

```cicsc
entity Ticket:
    states: [Open, InProgress, Resolved, Closed]
    initial: Open

    attr title: string
    attr description: string optional
    attr assignee: string optional

    command Assign:
        input user_id: string
        when state is Open or state is InProgress
        emit Assigned(assignee: input.user_id)

    command Resolve:
        input comment: string
        when state is InProgress
        emit Resolved(comment: input.comment)
```

## 2. Compile and Install

Use the CLI to compile your spec into a bundle and install it for a tenant:

```bash
cicsc compile ticketing.cicsc --out ticketing.v1.json
cicsc bind --tenant my-org --bundle ticketing.v1.json
cicsc install --tenant my-org
```

## 3. Interact via API

### Create a Ticket
Since we didn't define a `Create` command, CICSC relies on the implicit `Created` event if we used the `install-from-spec` helper, or we can add an explicit `Create` command.

Let's assume we have an `Open` command:

```bash
curl -X POST http://localhost:3000/cmd/Ticket/Open \
  -d '{
    "tenant_id": "my-org",
    "entity_id": "ticket-1",
    "command_id": "cmd-001",
    "input": { "title": "Fix the printer", "description": "It's jamming again" }
  }'
```

### Querying Tickets

Execute the default `All` view or define a custom one:

```bash
curl http://localhost:3000/view/OpenTickets?tenant_id=my-org
```

## 4. Observations

- Note how **state** is managed automatically. You cannot `Resolve` a ticket that hasn't been `InProgress`.
- Invariants are checked at every step. If you added a constraint that a user can only have 5 assigned tickets, the `Assign` command would fail transactionally.
