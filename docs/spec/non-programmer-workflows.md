# Non-Programmer Workflow Authoring (Phase 5)

This guide describes how a domain operator can author a workflow in Spec DSL
without touching Core IR directly.

## 1. Ticket Intake Workflow

Intent:
- New ticket starts in `new`.
- Agent can open ticket to `triage`.
- View groups tickets by lane.

Minimal Spec pattern:

```json
{
  "version": 0,
  "entities": {
    "Ticket": {
      "id": "string",
      "states": ["new", "triage", "done"],
      "initial": "new",
      "attributes": {
        "title": { "type": "string" },
        "lane": { "type": "string", "default": "todo" }
      },
      "commands": {
        "open": {
          "when": { "state_is": "new", "all": [{ "role_is": "agent" }] },
          "emit": [{ "type": "ticket_opened", "payload": {} }]
        }
      },
      "reducers": {
        "ticket_opened": [{ "set_state": "triage" }]
      }
    }
  }
}
```

## 2. CRM Lead Progression

Intent:
- Lead moves from `new` -> `qualified` -> `won`.
- Only owner role can advance state.

Pattern:
- Use `role_is` in command guards.
- Emit explicit events for each transition.
- Keep reducer transitions explicit and deterministic.

## 3. Authoring Checklist

- Define states and initial state first.
- Add commands with business-language names (`open`, `qualify`, `close`).
- Add guards from intent (`state_is`, `role_is`) before writing reducers.
- Ensure every emitted event has a reducer.
- Add at least one operational view (`lanes` or metric query).

## 4. Validation Loop

1. Compile spec:
`node cli/cicsc.mjs compile --spec ./spec.json --server http://localhost`

2. Install and bind tenant:
`node cli/cicsc.mjs install --spec ./spec.json --tenant t1 --server http://localhost`

3. Verify invariants:
`node cli/cicsc.mjs verify --tenant t1 --server http://localhost`

If compile fails, use diagnostics path to fix only the indicated location.

## 5. Related Contract Artifacts

- `spec/contracts/spec-dsl-v1.fixture.json`
- `spec/contracts/spec-dsl-v1.ir.json`
- `spec/contracts/spec-dsl-v1.roundtrip.json`
