import type { InterviewState } from "./interview-engine"
import type { SpecV0, SpecAttrV0 } from "../../spec/ast"

export class TranslationEngine {
  /**
   * Generates the system prompt for the LLM to translate requirements into canonical Spec JSON.
   * DSL text is preview-only and non-canonical.
   */
  getCanonicalSpecSystemPrompt (): string {
    return `You are an expert CICSC Spec architect.
Your task is to translate natural language requirements into canonical CICSC Spec JSON.

Return only JSON matching SpecV0 shape.

Schema:
{
  "version": 0,
  "entities": { ... }
}

Rules:
1. Every entity must have states and initial.
2. commands/reducers must be internally consistent.
3. Types: string, int, float, bool, time, enum.
`
  }

  getSystemPrompt (): string {
    return this.getCanonicalSpecSystemPrompt()
  }

  /**
   * Generates the user prompt based on the interview draft.
   */
  getCanonicalSpecUserPrompt (state: InterviewState): string {
    let prompt = `Translate the following system requirements into canonical CICSC Spec JSON:\n\n`
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

  getUserPrompt (state: InterviewState): string {
    return this.getCanonicalSpecUserPrompt(state)
  }

  /**
   * Preview-only adapter: deterministic Surface DSL rendering from canonical interview state.
   * Non-canonical; canonical output is Spec JSON via translateToSpecJson.
   */
  toPreviewDsl (state: InterviewState): string {
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
   * Backward-compatible alias for preview-only DSL adapter.
   */
  translateToDSL (state: InterviewState): string {
    return this.toPreviewDsl(state)
  }

  translateToDSLPreview (state: InterviewState): string {
    return this.toPreviewDsl(state)
  }

  /**
   * Canonical translator output for intent-plane v1.
   * Produces Spec JSON (SpecV0) instead of DSL text.
   */
  toCanonicalSpecJson (state: InterviewState): SpecV0 {
    const entities: SpecV0["entities"] = {}

    for (const entity of state.entities) {
      const entityName = this.sanitize(entity.name)
      if (!entityName) continue

      const states = entity.states.map((s) => this.sanitize(s)).filter(Boolean)
      const initial = entity.initialState ? this.sanitize(entity.initialState) : states[0]

      const attributes: Record<string, SpecAttrV0> = {}
      for (const attr of entity.attrs) {
        const attrName = this.sanitize(attr.name)
        if (!attrName) continue
        attributes[attrName] = {
          type: this.normalizeAttrType(attr.type),
          optional: Boolean(attr.optional) || undefined,
        }
      }

      const commands: NonNullable<SpecV0["entities"][string]["commands"]> = {}
      const reducers: NonNullable<SpecV0["entities"][string]["reducers"]> = {}

      for (const cmd of entity.commands) {
        const cmdName = this.sanitize(cmd.name)
        if (!cmdName) continue

        const eventType = `${cmdName}ed`
        const input: Record<string, SpecAttrV0> = {}
        const payload: Record<string, any> = {}

        for (const i of cmd.inputs) {
          const inputName = this.sanitize(i.name)
          if (!inputName) continue
          input[inputName] = { type: this.normalizeAttrType(i.type) }
          payload[inputName] = { var: { input: inputName } }
        }

        commands[cmdName] = {
          inputs: input,
          when: cmd.fromState ? { state_is: this.sanitize(cmd.fromState) } : undefined,
          emit: [{ type: eventType, payload }],
        }
        reducers[eventType] = []
      }

      entities[entityName] = {
        id: "string",
        states,
        initial: initial ?? "",
        attributes,
        commands,
        reducers,
      }
    }

    return {
      version: 0,
      entities,
    }
  }

  translateToSpecJson (state: InterviewState): SpecV0 {
    return this.toCanonicalSpecJson(state)
  }

  /**
   * Validates the generated DSL string using the core parser.
   */
  validateDSL (dsl: string): { valid: boolean; error?: string } {
    try {
      // eslint-disable-next-line @typescript-eslint/no-var-requires
      const { parseDSL } = require("../../spec/parse-dsl")
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

  private normalizeAttrType (raw: string): SpecAttrV0["type"] {
    const t = String(raw || "").toLowerCase()
    if (t === "int" || t === "float" || t === "bool" || t === "time" || t === "enum") {
      return t
    }
    return "string"
  }
}
