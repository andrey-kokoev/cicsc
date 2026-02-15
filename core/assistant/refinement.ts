import { SpecV0 } from "../../spec/ast"

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
    // Similar to explainSpec but more structured/tabular if needed
    return this.explainSpec(spec) + "\nReady to deploy? Please type 'Approve' to proceed."
  }
}
