import type { SpecV0 } from "./ast"

export type SpecTypeError = {
  path: string
  message: string
}

export type SpecTypecheckResult =
  | { ok: true }
  | { ok: false; errors: SpecTypeError[] }

export function typecheckSpecV0 (spec: SpecV0): SpecTypecheckResult {
  const errors: SpecTypeError[] = []

  for (const [entityName, e] of Object.entries(spec.entities ?? {})) {
    if (!Array.isArray(e.states) || e.states.length === 0) {
      errors.push({ path: `entities.${entityName}.states`, message: "states must be non-empty array" })
    } else if (!e.states.includes(e.initial)) {
      errors.push({ path: `entities.${entityName}.initial`, message: "initial must be one of states" })
    }

    for (const [cmdName, c] of Object.entries(e.commands ?? {})) {
      if (!Array.isArray((c as any).emit) || (c as any).emit.length === 0) {
        errors.push({ path: `entities.${entityName}.commands.${cmdName}.emit`, message: "emit must be non-empty array" })
      }
    }

    const reducerEvents = new Set(Object.keys(e.reducers ?? {}))
    for (const [cmdName, c] of Object.entries(e.commands ?? {})) {
      for (const emit of ((c as any).emit ?? []) as any[]) {
        const eventType = String((emit as any).type ?? "")
        if (!eventType) continue
        if (!reducerEvents.has(eventType)) {
          errors.push({
            path: `entities.${entityName}.commands.${cmdName}.emit`,
            message: `missing reducer for emitted event '${eventType}'`,
          })
        }
      }
    }
  }

  if (errors.length) return { ok: false, errors }
  return { ok: true }
}
