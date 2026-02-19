import { describe, it } from "node:test"
import assert from "node:assert/strict"

import { InterviewEngine } from "../../core/assistant/interview-engine.ts"
import { TranslationEngine } from "../../core/assistant/translate.ts"
import { RefinementEngine } from "../../core/assistant/refinement.ts"
import { typecheckSpecV0 } from "../../spec/typecheck.ts"

describe("intent-plane v1 contract", () => {
  it("tracks blocking issues and marks complete interview as deployable", () => {
    const interview = new InterviewEngine()

    const start = interview.getState()
    assert.ok(start.blockingIssues.length > 0)

    assert.equal(interview.processInput("ticketing"), null) // GREETING -> DOMAIN
    assert.equal(interview.processInput("ticketing"), null) // DOMAIN -> ENTITIES
    assert.equal(interview.processInput("Ticket"), null)
    assert.equal(interview.processInput("New, Closed"), null)
    assert.equal(interview.processInput("title string"), null)
    assert.equal(interview.processInput("Create"), null)

    const done = interview.getState()
    assert.equal(done.currentStep, "CONFIRM")
    assert.equal(done.blockingIssues.length, 0)

    assert.match(
      interview.processInput("yes") ?? "",
      /specification is ready|\/spec/i
    )
  })

  it("emits canonical Spec JSON from interview state", () => {
    const interview = new InterviewEngine()
    interview.processInput("ticketing")
    interview.processInput("ticketing")
    interview.processInput("Ticket")
    interview.processInput("New, Closed")
    interview.processInput("title string")
    interview.processInput("Create")

    const state = interview.getState()
    const translator = new TranslationEngine()
    const spec = translator.translateToSpecJson(state)

    assert.equal(spec.version, 0)
    assert.ok(spec.entities.Ticket)
    assert.ok(spec.entities.Ticket.commands?.Create)
    assert.ok(spec.entities.Ticket.reducers?.Createed)

    const tc = typecheckSpecV0(spec)
    assert.equal(tc.ok, true)
  })

  it("keeps DSL rendering as preview adapter while Spec JSON remains canonical", () => {
    const interview = new InterviewEngine()
    interview.processInput("ticketing")
    interview.processInput("ticketing")
    interview.processInput("Ticket")
    interview.processInput("New, Closed")
    interview.processInput("title string")
    interview.processInput("Create")

    const state = interview.getState()
    const translator = new TranslationEngine()
    const spec = translator.translateToSpecJson(state)
    const dslPreview = translator.translateToDSLPreview(state)

    assert.equal(spec.version, 0)
    assert.ok(spec.entities.Ticket)
    assert.match(dslPreview, /entity Ticket:/)
  })

  it("accepts non-additive refinement intents (rename) for full-range editing", () => {
    const refiner = new RefinementEngine()

    const intent = refiner.detectIntent("rename Ticket to Case")
    assert.equal(intent.type, "RENAME_ENTITY")

    const out = refiner.processEvolutionRequest(
      "rename Ticket to Case",
      {
        version: 0,
        entities: {
          Ticket: {
            id: "string",
            states: ["New"],
            initial: "New",
            attributes: {},
            commands: {
              Create: {
                inputs: {},
                emit: [{ type: "Created", payload: {} }],
              },
            },
            reducers: {
              Created: [],
            },
          },
        },
      },
      0
    )

    assert.equal(out.intent.type, "RENAME_ENTITY")
    assert.ok(out.migration)
    assert.equal(out.migration?.on_type, "Ticket")
    assert.deepEqual(out.blockingIssues, [])
  })

  it("keeps interview step stable on ambiguous input and returns clarification", () => {
    const interview = new InterviewEngine()
    const before = interview.getState()
    assert.equal(before.currentStep, "GREETING")

    const response = interview.processInput("maybe")
    assert.match(response ?? "", /examples|purpose|direction/i)

    const after = interview.getState()
    assert.equal(after.currentStep, "GREETING")
    assert.equal(after.entities.length, 0)
  })

  it("handles conflicting multi-edit evolution request deterministically", () => {
    const refiner = new RefinementEngine()
    const spec = {
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["New"],
          initial: "New",
          attributes: {},
          commands: {
            Create: {
              inputs: {},
              emit: [{ type: "Created", payload: {} }],
            },
          },
          reducers: {
            Created: [],
          },
        },
      },
    } as const

    const out = refiner.processEvolutionRequest(
      "rename Ticket to Case and add field priority to Ticket",
      spec as any,
      0
    )

    assert.equal(out.intent.type, "ADD_FIELD")
    assert.ok(out.migration)
    assert.equal(out.migration?.on_type, "Ticket")
    assert.equal(out.verification.safe, true)
    assert.deepEqual(out.blockingIssues, [])
  })

  it("reports specific blocking-issue quality for incomplete entities", () => {
    const interview = new InterviewEngine()
    interview.processInput("ticketing")
    interview.processInput("ticketing")
    interview.processInput("Ticket")

    const state = interview.getState()
    assert.ok(state.blockingIssues.some((s) => s.code === "MISSING_STATES" && s.path.includes("$.entities[0].states")))
    assert.ok(state.blockingIssues.some((s) => s.code === "MISSING_INITIAL_STATE" && s.path.includes("$.entities[0].initialState")))
    assert.ok(state.blockingIssues.some((s) => s.code === "MISSING_COMMANDS" && s.path.includes("$.entities[0].commands")))
  })

  it("uses per-intent non-additive migration strategy for remove-state", () => {
    const refiner = new RefinementEngine()
    const spec = {
      version: 0,
      entities: {
        Ticket: {
          id: "string",
          states: ["New", "Closed"],
          initial: "New",
          attributes: {},
          commands: {
            Close: {
              inputs: {},
              emit: [{ type: "Closed", payload: {} }],
            },
          },
          reducers: {
            Closed: [],
          },
        },
      },
    } as const

    const out = refiner.processEvolutionRequest(
      "remove state Closed from Ticket",
      spec as any,
      0
    )

    assert.equal(out.intent.type, "REMOVE_STATE")
    assert.ok(out.migration)
    assert.equal(out.migration?.on_type, "Ticket")
    assert.equal(out.migration?.state_map?.Closed, "New")
  })

  it("parses structured refinement intent grammar before pattern fallback", () => {
    const refiner = new RefinementEngine()
    const intent = refiner.detectIntent("intent=ADD_FIELD entity=Ticket field=priority field_type=int")
    assert.equal(intent.type, "ADD_FIELD")
    assert.equal((intent as any).entity, "Ticket")
    assert.equal((intent as any).field, "priority")
    assert.equal((intent as any).fieldType, "int")
  })
})
