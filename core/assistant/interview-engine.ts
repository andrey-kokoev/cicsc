export type InterviewState = {
  domain?: string
  entities: EntityDraft[]
  currentStep: "GREETING" | "DOMAIN" | "ENTITIES" | "STATES" | "ATTRIBUTES" | "COMMANDS" | "CONFIRM"
  currentEntityIndex: number
  pendingClarifications: string[]
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

export const QUESTION_TEMPLATES = {
  GREETING: [
    "Hi! I'm the CICSC Assistant. I'll help you design your system. What are we building today?",
    "Welcome! I assist with defining socio-technical control systems. What kind of project do you have in mind?",
    "Hello! I'm here to help you create a specification. What system would you like to build?"
  ],
  DOMAIN: [
    "What domain is this for? (e.g., ticketing, CRM, inventory management)",
    "What kind of organization or process are we modeling?",
    "Tell me about your system - what does it do?"
  ],
  ENTITIES: [
    "What are the main entities or objects we need to track? (e.g., Ticket, User, Order)",
    "What things does your system manage? List the key nouns.",
    "What are the core entities in your domain?"
  ],
  STATES: [
    "What states can {entity} be in? (e.g., open, in progress, resolved)",
    "What are the possible statuses for {entity}?",
    "How does {entity} progress through its lifecycle?"
  ],
  ATTRIBUTES: [
    "What information should we track about {entity}? (e.g., title, priority, assignee)",
    "What details are relevant for {entity}?",
    "What attributes describe a {entity}?"
  ],
  COMMANDS: [
    "What actions can be performed on {entity}? (e.g., create, update, close)",
    "What operations change {entity}'s state?",
    "What can someone do with a {entity}?"
  ],
  CONFIRM: [
    "Here's what I've gathered. Does this look right?",
    "Let me confirm what we've discussed. Is this accurate?",
    "Review your specification below and let me know if anything needs changes."
  ]
}

const AMBIGUITY_PATTERNS = [
  { pattern: /not sure|i don't know|unsure|maybe/i, response: "That's okay! Let me give you some examples. For a ticketing system, you might have entities like 'Ticket' or 'User'." },
  { pattern: /whatever|anything|i guess|doesn't matter/i, response: "I need a bit more direction. What's the main purpose of this system?" },
  { pattern: /like\s+\w+/i, response: "Could you be more specific? Try naming the actual entities." },
  { pattern: /and\s+something\s+else/i, response: "Sure, we can add more. What else is important?" },
  { pattern: /^$/i, response: "I didn't catch that. Could you try again?" },
  { pattern: /^[a-z]{1,2}$/i, response: "That's a bit short. Can you elaborate?" }
]

export class InterviewEngine {
  private state: InterviewState = {
    entities: [],
    currentStep: "GREETING",
    currentEntityIndex: -1,
    pendingClarifications: []
  }

  private detailStep: "STATES" | "ATTRIBUTES" | "COMMANDS" = "STATES"

  getNextQuestion (): string {
    switch (this.state.currentStep) {
      case "GREETING":
        return this.randomQuestion("GREETING")
      case "DOMAIN":
        return this.randomQuestion("DOMAIN")
      case "ENTITIES":
        return this.randomQuestion("ENTITIES")
      case "STATES":
      case "ATTRIBUTES":
      case "COMMANDS": {
        const entity = this.state.entities[this.state.currentEntityIndex]
        if (!entity) return this.randomQuestion("CONFIRM")
        const template = this.randomQuestion(this.state.currentStep)
        return template.replace(/{entity}/g, entity.name.toLowerCase())
      }
      case "CONFIRM":
        return this.randomQuestion("CONFIRM")
    }
  }

  private randomQuestion (step: keyof typeof QUESTION_TEMPLATES): string {
    const questions = QUESTION_TEMPLATES[step]
    return questions[Math.floor(Math.random() * questions.length)]!
  }

  handleAmbiguity (input: string): string | null {
    if (!input || input.trim().length === 0) {
      return "I didn't catch that. Could you try again?"
    }
    
    for (const { pattern, response } of AMBIGUITY_PATTERNS) {
      if (pattern.test(input)) {
        return response
      }
    }
    
    if (input.length < 3) {
      return "That's quite short. Could you provide more details?"
    }
    
    if (input.includes("?") && input.split("?").length > 3) {
      return "You're asking multiple questions. Let's focus on one at a time."
    }
    
    return null
  }

  processInput (input: string): string | null {
    const ambiguityResponse = this.handleAmbiguity(input)
    if (ambiguityResponse) return ambiguityResponse

    switch (this.state.currentStep) {
      case "GREETING":
        this.state.domain = input
        this.state.currentStep = "DOMAIN"
        break
        
      case "DOMAIN":
        this.state.domain = input
        this.state.currentStep = "ENTITIES"
        break
        
      case "ENTITIES":
        const names = input.split(/[,;and]+/).map(s => s.trim()).filter(Boolean)
        if (names.length === 0) {
          return "Please provide at least one entity."
        }
        this.state.entities = names.map(name => ({
          name: this.capitalize(name),
          states: [],
          attrs: [],
          commands: []
        }))
        this.state.currentEntityIndex = 0
        this.detailStep = "STATES"
        this.state.currentStep = "STATES"
        break
        
      case "STATES": {
        const states = input.split(/[,;]+/).map(s => s.trim()).filter(Boolean)
        if (states.length === 0) {
          return "Please provide at least one state."
        }
        const entity = this.state.entities[this.state.currentEntityIndex]!
        entity.states = states.map(s => this.capitalize(s))
        entity.initialState = entity.states[0]
        this.detailStep = "ATTRIBUTES"
        this.state.currentStep = "ATTRIBUTES"
        break
      }
      
      case "ATTRIBUTES": {
        const attrs = this.parseAttributes(input)
        if (attrs.length === 0) {
          return "Please provide attributes in format: 'name type' (e.g., 'title string', 'price int')"
        }
        const entity = this.state.entities[this.state.currentEntityIndex]!
        entity.attrs = attrs
        this.detailStep = "COMMANDS"
        this.state.currentStep = "COMMANDS"
        break
      }
      
      case "COMMANDS": {
        const commands = this.parseCommands(input, this.state.entities[this.state.currentEntityIndex]!)
        if (commands.length === 0) {
          return "Please provide commands in format: 'Create, Update, Delete' or 'fromState -> toState'"
        }
        const entity = this.state.entities[this.state.currentEntityIndex]!
        entity.commands = commands
        
        this.state.currentEntityIndex++
        if (this.state.currentEntityIndex >= this.state.entities.length) {
          this.state.currentStep = "CONFIRM"
        } else {
          this.detailStep = "STATES"
          this.state.currentStep = "STATES"
        }
        break
      }
      
      case "CONFIRM":
        if (input.toLowerCase().includes("yes") || input.toLowerCase().includes("correct") || input.toLowerCase().includes("right")) {
          return "Great! Your specification is ready. Type '/spec' to see the generated spec."
        } else if (input.toLowerCase().includes("no") || input.toLowerCase().includes("wrong")) {
          this.state.currentStep = "GREETING"
          this.state.entities = []
          this.state.currentEntityIndex = -1
          return "No problem! Let's start over. What are we building today?"
        }
        return "Please answer 'yes' or 'no' to confirm."
    }
    
    return null
  }

  private parseAttributes (input: string): { name: string; type: string; optional: boolean }[] {
    const attrs: { name: string; type: string; optional: boolean }[] = []
    const parts = input.split(/[,;]+/)
    
    for (const part of parts) {
      const trimmed = part.trim()
      if (!trimmed) continue
      
      const match = trimmed.match(/^(\w+)\s+(string|int|float|bool|time|enum)(?:\s+\(?optional\)?)?$/i)
      if (match) {
        attrs.push({
          name: match[1]!.toLowerCase(),
          type: match[2]!.toLowerCase(),
          optional: /optional/i.test(trimmed)
        })
      } else if (/^\w+$/.test(trimmed)) {
        attrs.push({ name: trimmed.toLowerCase(), type: "string", optional: false })
      }
    }
    
    return attrs
  }

  private parseCommands (input: string, entity: EntityDraft): CommandDraft[] {
    const commands: CommandDraft[] = []
    const parts = input.split(/[,;]+/)
    
    for (const part of parts) {
      const trimmed = part.trim()
      if (!trimmed) continue
      
      if (/^(\w+)\s*->\s*(\w+)$/i.test(trimmed)) {
        const match = trimmed.match(/^(\w+)\s*->\s*(\w+)$/i)
        if (match && entity.states.includes(match[1]!) && entity.states.includes(match[2]!)) {
          commands.push({
            name: `To${match[2]}`,
            fromState: match[1]!,
            toState: match[2]!,
            inputs: []
          })
        }
      } else if (/^\w+$/.test(trimmed)) {
        commands.push({
          name: this.capitalize(trimmed),
          fromState: entity.initialState || "",
          toState: undefined,
          inputs: []
        })
      }
    }
    
    return commands
  }

  private capitalize (str: string): string {
    return str.charAt(0).toUpperCase() + str.slice(1).toLowerCase()
  }

  getSummary (): string {
    let summary = `# System Specification: ${this.state.domain || "Untitled"}\n\n`
    
    summary += `## Entities (${this.state.entities.length})\n\n`
    
    for (const e of this.state.entities) {
      summary += `### ${e.name}\n`
      summary += `- **Initial State**: ${e.initialState || "N/A"}\n`
      summary += `- **States**: ${e.states.join(", ") || "None defined"}\n`
      summary += `- **Attributes**:\n`
      for (const a of e.attrs) {
        summary += `  - ${a.name}: ${a.type}${a.optional ? " (optional)" : ""}\n`
      }
      if (e.attrs.length === 0) summary += `  - None defined\n`
      summary += `- **Commands**:\n`
      for (const c of e.commands) {
        summary += `  - ${c.name}`
        if (c.fromState && c.toState) summary += ` (${c.fromState} → ${c.toState})`
        summary += "\n"
      }
      if (e.commands.length === 0) summary += `  - None defined\n`
      summary += "\n"
    }
    
    summary += `---\n`
    summary += `_Generated by CICSC Assistant_`
    
    return summary
  }
  
  getStructuredSpec (): object {
    return {
      version: 0,
      domain: this.state.domain,
      entities: Object.fromEntries(
        this.state.entities.map(e => [
          e.name,
          {
            id: "string",
            states: e.states,
            initial: e.initialState,
            attributes: Object.fromEntries(
              e.attrs.map(a => [a.name, { type: a.type, optional: a.optional }])
            ),
            commands: Object.fromEntries(
              e.commands.map(c => [c.name, { from: c.fromState, to: c.toState }])
            )
          }
        ])
      )
    }
  }
}
