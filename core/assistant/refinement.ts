import type { SpecV0 } from "../../spec/ast"
import type { MigrationSpecV0, EventTransformV0 } from "../ir/types"

export type ChangeIntent = 
  | { type: "ADD_FIELD"; entity: string; field: string; fieldType: string }
  | { type: "ADD_STATE"; entity: string; state: string }
  | { type: "REMOVE_STATE"; entity: string; state: string }
  | { type: "ADD_COMMAND"; entity: string; command: string }
  | { type: "RENAME_ENTITY"; oldName: string; newName: string }
  | { type: "ADD_ENTITY"; entity: string }
  | { type: "UNKNOWN"; raw: string }

const CHANGE_PATTERNS = [
  { pattern: /add (?:a )?(?:new )?(?:field|attribute|property)\s+"?(\w+)"?\s+(?:to|for)\s+(\w+)/i, type: "ADD_FIELD", extract: (m: RegExpMatchArray) => ({ field: m[1]!, entity: m[2]!, fieldType: "string" }) },
  { pattern: /add (?:new )?state\s+"?(\w+)"?\s+(?:to|for)\s+(\w+)/i, type: "ADD_STATE", extract: (m: RegExpMatchArray) => ({ state: m[1]!, entity: m[2]! }) },
  { pattern: /remove (?:the )?state\s+"?(\w+)"?\s+from\s+(\w+)/i, type: "REMOVE_STATE", extract: (m: RegExpMatchArray) => ({ state: m[1]!, entity: m[2]! }) },
  { pattern: /add (?:new )?command\s+"?(\w+)"?\s+(?:to|for)\s+(\w+)/i, type: "ADD_COMMAND", extract: (m: RegExpMatchArray) => ({ command: m[1]!, entity: m[2]! }) },
  { pattern: /rename\s+(\w+)\s+(?:to|as)\s+(\w+)/i, type: "RENAME_ENTITY", extract: (m: RegExpMatchArray) => ({ oldName: m[1]!, newName: m[2]! }) },
  { pattern: /add (?:new )?entity\s+"?(\w+)"?/i, type: "ADD_ENTITY", extract: (m: RegExpMatchArray) => ({ entity: m[1]! }) },
  { pattern: /add (?:a )?(?:new )?(field|attribute|property)\s+"?(\w+)"?/i, type: "ADD_FIELD", extract: (m: RegExpMatchArray) => ({ field: m[2]!, entity: "unknown", fieldType: "string" }) },
]

type PlannerContext = {
  currentSpec: SpecV0
  intent: ChangeIntent
  fromVersion: number
  toVersion: number
}

export class RefinementEngine {
  /**
   * Explains a Spec in plain English (BG3.3).
   */
  explainSpec (spec: SpecV0): string {
    let explanation = "This system defines the following:\n\n"
    for (const [name, entity] of Object.entries(spec.entities)) {
      explanation += `Entity: ${name}\n`
      explanation += `- It can be in these states: ${entity.states.join(", ")}.\n`
      explanation += `- It starts in the '${entity.initial}' state.\n`
      if (Object.keys(entity.attributes || {}).length > 0) {
        explanation += `- It tracks these details: ${Object.keys(entity.attributes!).join(", ")}.\n`
      }
      if (Object.keys(entity.commands || {}).length > 0) {
        explanation += `- You can perform these actions: ${Object.keys(entity.commands!).join(", ")}.\n`
      }
      explanation += "\n"
    }
    return explanation
  }

  /**
   * Generates a prompt for natural language edits (BG3.2).
   */
  getRefinementPrompt (dsl: string, editInstruction: string): string {
    return `Update the following CICSC Spec DSL based on this request: "${editInstruction}"

Current DSL:
${dsl}

Rules:
1. Maintain the existing structure and indentation.
2. Only change what is requested.
3. Ensure the result is valid CICSC Spec DSL.
`
  }

  /**
   * Returns a human-readable preview of what will be built (BG3.1).
   */
  getPreview (spec: SpecV0): string {
    return this.explainSpec(spec) + "\nReady to deploy? Please type 'Approve' to proceed."
  }

  /**
   * BG4.1: Detect intent to change from natural language
   */
  detectIntent (input: string): ChangeIntent {
    for (const { pattern, type, extract } of CHANGE_PATTERNS) {
      const match = input.match(pattern)
      if (match) {
        const extracted = extract(match)
        return { type: type as ChangeIntent["type"], ...extracted } as ChangeIntent
      }
    }
    return { type: "UNKNOWN", raw: input }
  }

  /**
   * BG4.2: Generate migration spec from natural language change intent
   */
  generateMigrationSpec (
    currentSpec: SpecV0,
    intent: ChangeIntent,
    fromVersion: number,
    toVersion: number
  ): MigrationSpecV0 | null {
    const planners: Record<ChangeIntent["type"], (ctx: PlannerContext) => MigrationSpecV0 | null> = {
      ADD_FIELD: (ctx) => {
        const entityName = "entity" in ctx.intent ? ctx.intent.entity : null
        if (!entityName || entityName === "unknown" || !ctx.currentSpec.entities[entityName]) return null
        const fieldName = (ctx.intent as any).field
        return {
          from_version: ctx.fromVersion,
          to_version: ctx.toVersion,
          on_type: entityName,
          event_transforms: {
            "*": { payload_map: { [fieldName]: { lit: { null: true } } } },
          },
          state_map: {},
        }
      },
      ADD_STATE: (ctx) => {
        const entityName = "entity" in ctx.intent ? ctx.intent.entity : null
        if (!entityName || entityName === "unknown" || !ctx.currentSpec.entities[entityName]) return null
        return {
          from_version: ctx.fromVersion,
          to_version: ctx.toVersion,
          on_type: entityName,
          event_transforms: { "*": { drop: false } },
          state_map: {},
        }
      },
      REMOVE_STATE: (ctx) => {
        const entityName = "entity" in ctx.intent ? ctx.intent.entity : null
        if (!entityName || entityName === "unknown") return null
        const entity = ctx.currentSpec.entities[entityName]
        if (!entity) return null
        const removeState = (ctx.intent as any).state
        const fallback = entity.states.find((s) => s !== removeState) ?? ""
        return {
          from_version: ctx.fromVersion,
          to_version: ctx.toVersion,
          on_type: entityName,
          event_transforms: { "*": { drop: false } },
          state_map: { [removeState]: fallback },
        }
      },
      ADD_COMMAND: (ctx) => {
        const entityName = "entity" in ctx.intent ? ctx.intent.entity : null
        if (!entityName || entityName === "unknown" || !ctx.currentSpec.entities[entityName]) return null
        return {
          from_version: ctx.fromVersion,
          to_version: ctx.toVersion,
          on_type: entityName,
          event_transforms: { "*": { drop: false } },
          state_map: {},
        }
      },
      RENAME_ENTITY: (ctx) => {
        const oldName = (ctx.intent as any).oldName
        if (!ctx.currentSpec.entities[oldName]) return null
        return {
          from_version: ctx.fromVersion,
          to_version: ctx.toVersion,
          on_type: oldName,
          event_transforms: {},
          state_map: {},
        }
      },
      ADD_ENTITY: (_ctx) => null,
      UNKNOWN: (_ctx) => null,
    }

    const planner = planners[intent.type]
    if (!planner) return null
    return planner({ currentSpec, intent, fromVersion, toVersion })
  }

  /**
   * BG4.3: Verify migration preserves invariants (returns explanation)
   * Note: Full Lean verification would require external Lean process
   */
  verifyMigration (migration: MigrationSpecV0, spec: SpecV0): { safe: boolean; issues: string[] } {
    const issues: string[] = []
    const entity = spec.entities[migration.on_type]

    if (!entity) {
      issues.push(`Entity '${migration.on_type}' not found in spec`)
      return { safe: issues.length === 0, issues }
    }

    for (const [eventType, transform] of Object.entries(migration.event_transforms)) {
      if (transform.drop) {
        if (eventType === "*") {
          issues.push(`Migration drops all events - data loss warning`)
        }
      }
    }

    if (migration.state_map) {
      const removedStates = Object.values(migration.state_map).filter(s => s === null || s === undefined || s === "")
      if (removedStates.length > 0) {
        issues.push(`State map removes states without replacement`)
      }
    }

    return { safe: issues.length === 0, issues }
  }

  /**
   * BG4.4: Apply migration and generate confirmation message
   */
  applyMigration (migration: MigrationSpecV0): string {
    let message = `# Migration Ready\n\n`
    message += `**From Version**: ${migration.from_version}\n`
    message += `**To Version**: ${migration.to_version}\n`
    message += `**Entity**: ${migration.on_type}\n\n`

    message += `**Event Transforms**:\n`
    for (const [eventType, transform] of Object.entries(migration.event_transforms)) {
      message += `- ${eventType}: `
      if (transform.drop) {
        message += "DROP\n"
      } else if (transform.emit_as) {
        message += `emit as ${transform.emit_as}\n`
      } else if (transform.payload_map) {
        message += `map fields: ${Object.keys(transform.payload_map).join(", ")}\n`
      } else {
        message += "pass-through\n"
      }
    }

    if (migration.state_map && Object.keys(migration.state_map).length > 0) {
      message += `\n**State Mappings**:\n`
      for (const [oldState, newState] of Object.entries(migration.state_map)) {
        message += `- ${oldState} → ${newState || "(removed)"}\n`
      }
    }

    message += `\n---\n_Type "Approve" to apply this migration, or "Cancel" to abort._`
    return message
  }

  /**
   * Full BG4 pipeline: detect → generate → verify → confirm
   */
  processEvolutionRequest (
    input: string,
    currentSpec: SpecV0,
    currentVersion: number
  ): {
    intent: ChangeIntent
    migration: MigrationSpecV0 | null
    verification: { safe: boolean; issues: string[] }
    confirmation: string
    blockingIssues: string[]
  } {
    const intent = this.detectIntent(input)
    const nextVersion = currentVersion + 1
    const migration = this.generateMigrationSpec(currentSpec, intent, currentVersion, nextVersion)
    const verification = migration ? this.verifyMigration(migration, currentSpec) : { safe: false, issues: ["Could not generate migration"] }
    const confirmation = migration ? this.applyMigration(migration) : "Sorry, I couldn't understand that change. Try something like 'Add a new field to Ticket'."
    const blockingIssues = verification.safe ? [] : [...verification.issues]

    return { intent, migration, verification, confirmation, blockingIssues }
  }
}
