import { InterviewState, EntityDraft, CommandDraft } from "./interview-engine"
import { parseDSL } from "../../spec/parse-dsl"

export class TranslationEngine {
  /**
   * Generates the system prompt for the LLM to translate requirements into Spec DSL.
   */
  getSystemPrompt (): string {
    return `You are an expert CICSC Spec architect.
Your task is to translate natural language requirements into the CICSC Surface DSL.

The Surface DSL is indentation-aware (4 spaces).

Grammar:
entity <EntityName>:
    states: [<State1>, <State2>]
    initial: <State1>

    attr <attrName>: <type> [optional]

    command <CommandName>:
        input <inputName>: <type>
        when state is <CurrentState>
        emit <EventName>(<field>: input.<inputName>)

Types: string, int, float, bool, time.

Rules:
1. Every entity must have 'states:' and 'initial:'.
2. Indentation is mandatory.
3. Use 'attr' for fields.
`
  }

  /**
   * Generates the user prompt based on the interview draft.
   */
  getUserPrompt (state: InterviewState): string {
    let prompt = `Translate the following system requirements into CICSC Spec DSL:\n\n`
    prompt += `Domain: ${state.domain}\n`
    for (const entity of state.entities) {
      prompt += `Entity: ${entity.name}\n`
      prompt += `- States: ${entity.states.join(", ")}\n`
      if (entity.initialState) prompt += `- Initial State: ${entity.initialState}\n`
      for (const attr of entity.attrs) {
        prompt += `- Attribute: ${attr.name} (${attr.type}${attr.optional ? ", optional" : ""})\n`
      }
      for (const cmd of entity.commands) {
        prompt += `- Command: ${cmd.name} (from ${cmd.fromState}${cmd.toState ? " to " + cmd.toState : ""})\n`
        for (const input of cmd.inputs) {
          prompt += `  - Input: ${input.name} (${input.type})\n`
        }
      }
    }
    return prompt
  }

  /**
   * Simple deterministic translator for basic cases (fallback/verification).
   */
  translateToDSL (state: InterviewState): string {
    let dsl = ""
    for (const entity of state.entities) {
      dsl += `entity ${this.sanitize(entity.name)}:\n`
      dsl += `    states: [${entity.states.map(s => this.sanitize(s)).join(", ")}]\n`
      if (entity.initialState) {
        dsl += `    initial: ${this.sanitize(entity.initialState)}\n`
      }
      dsl += "\n"
      for (const attr of entity.attrs) {
        const opt = attr.optional ? " optional" : ""
        dsl += `    attr ${this.sanitize(attr.name)}: ${attr.type}${opt}\n`
      }
      for (const cmd of entity.commands) {
        dsl += `    command ${this.sanitize(cmd.name)}:\n`
        for (const input of cmd.inputs) {
          dsl += `        input ${this.sanitize(input.name)}: ${input.type}\n`
        }
        dsl += `        when state is ${this.sanitize(cmd.fromState)}\n`
        if (cmd.toState) {
          dsl += `        # Note: 'to' state is handled by reducers in CICSC, but we can emit an event here\n`
          dsl += `        emit ${this.sanitize(cmd.name)}ed(${cmd.inputs.map(i => `${i.name}: input.${i.name}`).join(", ")})\n`
        }
      }
      dsl += `\n`
    }
    return dsl
  }

  /**
   * Validates the generated DSL string using the core parser.
   */
  validateDSL (dsl: string): { valid: boolean; error?: string } {
    try {
      parseDSL(dsl)
      return { valid: true }
    } catch (e: any) {
      return { valid: false, error: e.message }
    }
  }

  /**
   * Generates multiple prompt variations for ambiguous cases.
   */
  getAlternativesPrompts (state: InterviewState): string[] {
    const base = this.getUserPrompt(state)
    return [
      `${base}\nOptional: Make it strictly role-based (RBAC).`,
      `${base}\nOptional: Focus on high-throughput performance.`,
      `${base}\nOptional: Add detailed audit logging for every command.`
    ]
  }

  private sanitize (name: string): string {
    return name.replace(/[^a-zA-Z0-9]/g, "")
  }
}
