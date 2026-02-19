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
})
