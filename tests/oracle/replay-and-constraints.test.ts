import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { verifyHistoryAgainstIr } from "../../core/runtime/verify"

describe("oracle: replay + constraints", () => {
  it("replays events into snapshot and enforces snapshot constraint", () => {
    const bundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new", "triage", "closed"],
            initial_state: "new",
            attrs: {},
            commands: {},
            reducer: {
              created: [{ set_attr: { name: "title", expr: { var: { e_payload: { path: "title" } } } } }],
              triaged: [{ set_state: { expr: { lit: { string: "triage" } } } }],
            },
          },
        },
        constraints: {
          title_required: {
            kind: "snapshot",
            on_type: "Ticket",
            expr: { and: [{ not: { is_null: { var: { row: { field: "title" } } } } }, { ne: [{ var: { row: { field: "title" } } }, { lit: { string: "" } }] }] },
          },
        },
      },
    }

    const events = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "A",
        seq: 1,
        event_type: "created",
        payload: { title: "Hello" },
        ts: 10,
        actor_id: "u",
      },
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "A",
        seq: 2,
        event_type: "triaged",
        payload: {},
        ts: 11,
        actor_id: "u",
      },
    ]

    const report = verifyHistoryAgainstIr({
      bundle,
      events: events as any,
      now: 20,
      actor: "u",
      policies: {},
      intrinsics: {
        has_role: () => true,
        role_of: () => "agent",
        auth_ok: () => true,
        constraint: () => true,
        len: () => 0,
        str: (v) => (v === null ? null : String(v)),
        int: (v) => (typeof v === "number" ? Math.trunc(v) : null),
        float: (v) => (typeof v === "number" ? v : null),
      },
    })

    assert.equal(report.ok, true)
    assert.equal(report.entities_count, 1)
    assert.equal(report.constraints_count, 1)
    assert.equal(report.violations.length, 0)
  })

  it("fails snapshot constraint when missing title", () => {
    const bundle = {
      core_ir: {
        version: 0,
        types: {
          Ticket: {
            id_type: "string",
            states: ["new"],
            initial_state: "new",
            attrs: {},
            commands: {},
            reducer: {
              created: [{ set_attr: { name: "title", expr: { var: { e_payload: { path: "title" } } } } }],
            },
          },
        },
        constraints: {
          title_required: {
            kind: "snapshot",
            on_type: "Ticket",
            expr: { not: { is_null: { var: { row: { field: "title" } } } } },
          },
        },
      },
    }

    const events = [
      {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: "A",
        seq: 1,
        event_type: "created",
        payload: {},
        ts: 10,
        actor_id: "u",
      },
    ]

    const report = verifyHistoryAgainstIr({
      bundle,
      events: events as any,
      now: 20,
      actor: "u",
      policies: {},
      intrinsics: {
        has_role: () => true,
        role_of: () => "agent",
        auth_ok: () => true,
        constraint: () => true,
        len: () => 0,
        str: (v) => (v === null ? null : String(v)),
        int: (v) => (typeof v === "number" ? Math.trunc(v) : null),
        float: (v) => (typeof v === "number" ? v : null),
      },
    })

    assert.equal(report.ok, false)
    assert.equal(report.violations.length, 1)
    assert.equal(report.violations[0]!.constraint_id, "title_required")
  })
})
