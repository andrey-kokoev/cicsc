import type { SpecV0, SpecEntityV0, SpecAttrV0, SpecCommandV0, SpecViewV0, SpecConstraintV0 } from "./ast"

type Line = {
  indent: number
  text: string
  lineNum: number
}

export function parseDSL (input: string): SpecV0 {
  const lines: Line[] = input.split("\n").map((l, i) => {
    const match = l.match(/^(\s*)(.*)$/)
    return {
      indent: match![1].length,
      text: match![2].trim(),
      lineNum: i + 1
    }
  }).filter(l => l.text !== "" && !l.text.startsWith("#"))

  const spec: SpecV0 = {
    version: 0,
    entities: {},
    views: {},
    constraints: {},
  }

  let i = 0
  while (i < lines.length) {
    const line = lines[i]
    if (line.text.startsWith("entity ")) {
      const match = line.text.match(/^entity\s+(\w+):$/)
      if (!match) throw new Error(`Invalid entity declaration at line ${line.lineNum}`)
      const name = match[1]
      const { entity, nextIdx } = parseEntity(lines, i + 1)
      spec.entities[name] = entity
      i = nextIdx
    } else if (line.text.startsWith("view ")) {
      const match = line.text.match(/^view\s+(\w+):$/)
      if (!match) throw new Error(`Invalid view declaration at line ${line.lineNum}`)
      const name = match[1]
      const { view, nextIdx } = parseView(lines, i + 1)
      spec.views![name] = view
      i = nextIdx
    } else if (line.text.startsWith("constraint ")) {
      const match = line.text.match(/^constraint\s+(\w+):$/ || /^constraint:$/)
      if (!match) throw new Error(`Invalid constraint declaration at line ${line.lineNum}`)
      const name = match[1] || `constraint_${line.lineNum}`
      const { constraint, nextIdx } = parseConstraint(lines, i + 1)
      spec.constraints![name] = constraint
      i = nextIdx
    } else {
      throw new Error(`Unexpected top-level token "${line.text}" at line ${line.lineNum}`)
    }
  }

  return spec
}

function parseEntity (lines: Line[], startIdx: number): { entity: SpecEntityV0, nextIdx: number } {
  const entity: SpecEntityV0 = {
    id: "string",
    states: [],
    initial: "",
    attributes: {},
    commands: {},
  }
  const baseIndent = lines[startIdx]?.indent ?? 0
  let i = startIdx

  while (i < lines.length && lines[i].indent >= baseIndent) {
    const line = lines[i]
    if (line.text.startsWith("states:")) {
      const parts = line.text.replace("states:", "").replace("[", "").replace("]", "").split(",").map(s => s.trim())
      entity.states = parts
    } else if (line.text.startsWith("initial:")) {
      entity.initial = line.text.replace("initial:", "").trim()
    } else if (line.text.startsWith("attr ")) {
      const match = line.text.match(/^attr\s+(\w+)(?::\s*(\w+))?(?:\s+(optional))?$/)
      if (match) {
        const [_, name, type, optional] = match
        entity.attributes![name] = {
          type: (type || "string") as any,
          optional: optional === "optional"
        }
      }
    } else if (line.text.startsWith("command ")) {
      const match = line.text.match(/^command\s+(\w+):$/)
      if (match) {
        const name = match[1]
        const { command, nextIdx } = parseCommand(lines, i + 1)

        // Sugar: implicit emit if none provided
        if (command.emit.length === 0) {
          const payload: Record<string, any> = {}
          for (const inputName of Object.keys(command.inputs || {})) {
            payload[inputName] = { var: { input: { field: inputName } } }
          }
          command.emit.push({
            type: `${name}ed`,
            payload
          })
        }

        entity.commands![name] = command
        i = nextIdx - 1
      }
    }
    i++
  }

  if (!entity.initial && entity.states.length > 0) {
    entity.initial = entity.states[0]
  }

  return { entity, nextIdx: i }
}

function parseCommand (lines: Line[], startIdx: number): { command: SpecCommandV0, nextIdx: number } {
  const command: SpecCommandV0 = {
    inputs: {},
    emit: []
  }
  const baseIndent = lines[startIdx]?.indent ?? 0
  let i = startIdx

  while (i < lines.length && lines[i].indent >= baseIndent) {
    const line = lines[i]
    if (line.text.startsWith("input ")) {
      const match = line.text.match(/^input\s+(\w+):\s*(\w+)(?:\s+(optional))?$/)
      if (match) {
        const [_, name, type, optional] = match
        command.inputs![name] = {
          type: type as any,
          optional: optional === "optional"
        }
      }
    } else if (line.text.startsWith("when ")) {
      command.when = parseExpression(line.text.replace("when ", "").trim())
    } else if (line.text.startsWith("emit ")) {
      const emitText = line.text.replace("emit ", "").trim()
      const match = emitText.match(/^(\w+)(?:\((.*)\))?$/)
      if (match) {
        const [_, type, payloadStr] = match
        const payload: Record<string, any> = {}
        if (payloadStr) {
          payloadStr.split(",").forEach(p => {
            const [k, v] = p.split(":").map(s => s.trim())
            payload[k] = parseExpression(v)
          })
        }
        command.emit.push({ type, payload })
      }
    }
    i++
  }
  return { command, nextIdx: i }
}

function parseExpression (expr: string): any {
  // Simple expression parser for Surface -> IR
  // Supports: state is X, priority is P0, input x, attr y, etc.
  if (expr.includes(" is ")) {
    const [left, right] = expr.split(" is ").map(s => s.trim())
    return { eq: [parseTerm(left), parseTerm(right)] }
  }
  if (expr.includes(" is not ")) {
    const [left, right] = expr.split(" is not ").map(s => s.trim())
    return { ne: [parseTerm(left), parseTerm(right)] }
  }
  return parseTerm(expr)
}

function parseTerm (term: string): any {
  if (term === "state") return { var: { state: true } }
  if (term === "empty") return { lit: { null: true } }
  if (term.startsWith("'") || term.startsWith("\"")) return { lit: { string: term.slice(1, -1) } }
  if (!isNaN(Number(term))) return { lit: { int: Number(term) } }

  // Implicit context: check if it's a known identifier in next phase (typechecking)
  // For now, assume it's a literal string if it looks like a state/enum value (starts with uppercase)
  if (/^[A-Z]/.test(term)) return { lit: { string: term } }

  // Default to a variable if lowercase
  return { var: { input: { field: term } } }
}

function parseView (lines: Line[], startIdx: number): { view: SpecViewV0, nextIdx: number } {
  const view: any = { kind: "lanes" }
  const baseIndent = lines[startIdx]?.indent ?? 0
  let i = startIdx
  while (i < lines.length && lines[i].indent >= baseIndent) {
    const line = lines[i]
    if (line.text.startsWith("on ")) {
      view.on = line.text.replace("on ", "").trim()
    } else if (line.text.startsWith("where ")) {
      view.query = parseExpression(line.text.replace("where ", "").trim())
    } else if (line.text.startsWith("order_by ")) {
      const parts = line.text.replace("order_by ", "").trim().split(/\s+/)
      view.lanes = { order_by: { field: parts[0], dir: parts[1] || "asc" } }
    }
    i++
  }
  return { view, nextIdx: i }
}

function parseConstraint (lines: Line[], startIdx: number): { constraint: SpecConstraintV0, nextIdx: number } {
  const constraint: any = { kind: "bool_query" }
  const baseIndent = lines[startIdx]?.indent ?? 0
  let i = startIdx
  while (i < lines.length && lines[i].indent >= baseIndent) {
    const line = lines[i]
    if (line.text.startsWith("on ")) {
      constraint.entity = line.text.replace("on ", "").trim()
    } else if (line.text.startsWith("at ")) {
      constraint.kind = "snapshot"
    } else if (line.text.startsWith("when ")) {
      constraint.query = parseExpression(line.text.replace("when ", "").trim())
    } else if (line.text.startsWith("assert ")) {
      constraint.assert = parseExpression(line.text.replace("assert ", "").trim())
    }
    i++
  }
  return { constraint, nextIdx: i }
}
