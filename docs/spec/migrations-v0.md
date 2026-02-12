# /docs/spec/migrations-v0.md

# Migration Spec v0 (Normative)

## 0. Status

This document defines the v0 migration shape for Spec DSL and Core IR.

---

## 1. Purpose

A migration defines a total transform from history/version `N` to `N+1` for a given entity type:

- event-level transforms (`event_transforms`)
- optional state remapping (`state_map`)

---

## 2. Spec DSL Shape

```json
{
  "migrations": {
    "ticketing_v0_to_v1": {
      "from": 0,
      "to": 1,
      "entity": "Ticket",
      "event_transforms": {
        "ticket_created": {
          "emit_as": "ticket_opened",
          "payload_map": {
            "title": { "var": { "e_payload": { "path": "title" } } }
          }
        }
      },
      "state_map": {
        "open": "triage"
      }
    }
  }
}
```

---

## 3. Core IR Shape

```json
{
  "migrations": {
    "ticketing_v0_to_v1": {
      "from_version": 0,
      "to_version": 1,
      "on_type": "Ticket",
      "event_transforms": {
        "ticket_created": {
          "emit_as": "ticket_opened",
          "payload_map": {
            "title": { "var": { "e_payload": { "path": "title" } } }
          }
        }
      },
      "state_map": {
        "open": "triage"
      }
    }
  }
}
```

---

## 4. Semantics

- `from`/`to` and `from_version`/`to_version` define migration edge direction.
- `event_transforms[event_type]` rewrites old events into new events.
- `emit_as` defaults to source event type when omitted.
- `payload_map` is evaluated in event transform environment and must be deterministic.
- `drop: true` means the source event is omitted from migrated history.
- `state_map` remaps replayed state labels after migration.

Totality and executability are enforced by migration compiler/typechecker steps.
