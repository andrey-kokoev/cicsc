import { TranslationEngine } from "./core/assistant/translate"
import { InterviewState } from "./core/assistant/interview-engine"
import { RefinementEngine } from "./core/assistant/refinement"
import { parseDSL } from "../../spec/parse-dsl"

const engine = new TranslationEngine()
const refiner = new RefinementEngine()
const mockState: InterviewState = {
  domain: "Ticketing",
  entities: [
    {
      name: "Ticket",
      states: ["Open", "Closed"],
      initialState: "Open",
      attrs: [{ name: "title", type: "string", optional: false }],
      commands: [
        {
          name: "Resolve",
          fromState: "Open",
          toState: "Closed",
          inputs: [{ name: "comment", type: "string" }]
        }
      ]
    }
  ],
  currentStep: "CONFIRM",
  currentEntityIndex: 0
}

const dsl = engine.translateToDSL(mockState)
console.log("Generated DSL:\n", dsl)

const validation = engine.validateDSL(dsl)
console.log("Validation:", validation)

if (!validation.valid) {
  process.exit(1)
}

const spec = parseDSL(dsl)
console.log("\nExplanation:\n", refiner.explainSpec(spec))

const refinementPrompt = refiner.getRefinementPrompt(dsl, "Add a priority attribute")
console.log("\nRefinement Prompt Preview:\n", refinementPrompt)
