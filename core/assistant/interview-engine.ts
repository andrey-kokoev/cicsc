export type InterviewState = {
  domain?: string
  entities: EntityDraft[]
  currentStep: "DOMAIN" | "ENTITIES" | "DETAILS" | "CONFIRM"
  currentEntityIndex: number
}

export type EntityDraft = {
  name: string
  states: string[]
  initialState?: string
  attrs: { name: string; type: string; optional: boolean }[]
  commands: CommandDraft[]
}

export type CommandDraft = {
  name: string
  fromState: string
  toState?: string
  inputs: { name: string; type: string }[]
}

export class InterviewEngine {
  private state: InterviewState = {
    entities: [],
    currentStep: "DOMAIN",
    currentEntityIndex: -1
  };

  getNextQuestion (): string {
    switch (this.state.currentStep) {
      case "DOMAIN":
        return "Welcome to the CICSC Assistant. What kind of system are we building today?"
      case "ENTITIES":
        return `Got it, a ${this.state.domain}. What are the main objects or 'Entities' we need to track? (e.g., Ticket, User, Product)`
      case "DETAILS":
        const entity = this.state.entities[this.state.currentEntityIndex]
        if (!entity.states.length) {
          return `Let's look at ${entity.name}. What are the different statuses it can have? (e.g., Open, InProgress, Closed)`
        }
        if (entity.commands.length === 0) {
          return `What actions can someone take on a ${entity.name}? (e.g., 'Assign', 'Resolve')`
        }
        return `What details (attributes) should we track for ${entity.name}? (e.g., 'title' as string, 'price' as int)`
      case "CONFIRM":
        return "I've drafted your system. Does this look correct?"
    }
  }

  private handleAmbiguity (input: string): string | null {
    if (input.toLowerCase().includes("not sure") || input.length < 2) {
      return "Could you be a bit more specific? For example, if you're building a store, an entity might be 'Product' or 'Order'."
    }
    return null
  }

  processInput (input: string): string | null {
    const ambiguityError = this.handleAmbiguity(input)
    if (ambiguityError) return ambiguityError

    // Simple logic for state transitions
    if (this.state.currentStep === "DOMAIN") {
      this.state.domain = input
      this.state.currentStep = "ENTITIES"
    } else if (this.state.currentStep === "ENTITIES") {
      const names = input.split(",").map(s => s.trim())
      this.state.entities = names.map(name => ({
        name,
        states: [],
        attrs: [],
        commands: []
      }))
      this.state.currentStep = "DETAILS"
      this.state.currentEntityIndex = 0
    } else if (this.state.currentStep === "DETAILS") {
      const entity = this.state.entities[this.state.currentEntityIndex]!
      if (entity.states.length === 0) {
        entity.states = input.split(",").map(s => s.trim())
        entity.initialState = entity.states[0]
      } else {
        // Moving to next entity or next step
        this.state.currentEntityIndex++
        if (this.state.currentEntityIndex >= this.state.entities.length) {
          this.state.currentStep = "CONFIRM"
        }
      }
    }
  }

  getSummary (): string {
    let summary = `Okay, I've got it. We are building a ${this.state.domain}.\n`
    summary += `We'll have ${this.state.entities.length} entities: ${this.state.entities.map(e => e.name).join(", ")}.\n`
    for (const e of this.state.entities) {
      summary += `- ${e.name} starts as ${e.initialState} and can be in these states: [${e.states.join(", ")}].\n`
    }
    return summary
  }
}
