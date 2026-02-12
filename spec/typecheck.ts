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

  for (const [migrationName, mAny] of Object.entries((spec as any).migrations ?? {})) {
    const m = mAny as any
    const from = Number(m.from)
    const to = Number(m.to)
    if (!Number.isInteger(from) || !Number.isInteger(to) || to !== from + 1) {
      errors.push({
        path: `migrations.${migrationName}`,
        message: "migration must declare adjacent versions (from N to N+1)",
      })
    }

    const entityName = String(m.entity ?? "")
    const entity = (spec.entities ?? {})[entityName]
    if (!entity) {
      errors.push({
        path: `migrations.${migrationName}.entity`,
        message: `unknown entity '${entityName}'`,
      })
      continue
    }

    const emittedEvents = new Set<string>()
    for (const c of Object.values(entity.commands ?? {}) as any[]) {
      for (const em of (c.emit ?? []) as any[]) {
        const et = String(em?.type ?? "")
        if (et) emittedEvents.add(et)
      }
    }

    const eventTransforms = (m.event_transforms ?? {}) as Record<string, any>
    for (const eventType of emittedEvents) {
      if (eventTransforms[eventType]) continue
      errors.push({
        path: `migrations.${migrationName}.event_transforms`,
        message: `missing transform for emitted event '${eventType}'`,
      })
    }

    const stateMap = (m.state_map ?? {}) as Record<string, string>
    for (const state of entity.states ?? []) {
      if (typeof stateMap[state] === "string" && stateMap[state] !== "") continue
      errors.push({
        path: `migrations.${migrationName}.state_map`,
        message: `missing state mapping for '${state}'`,
      })
    }
  }

  if (errors.length) return { ok: false, errors }
  return { ok: true }
}
