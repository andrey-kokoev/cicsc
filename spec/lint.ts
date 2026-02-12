import type { SpecV0 } from "./ast"

export type SpecLintIssue = {
  code:
    | "ANTI_PATTERN_UNSCOPED_COMMAND"
    | "ANTI_PATTERN_MULTI_EMIT"
    | "ANTI_PATTERN_MULTIPLE_STATE_WRITES"
    | "UNREACHABLE_STATE"
    | "DEAD_COMMAND"
  path: string
  message: string
  severity: "warning"
}

export type SpecLintResult = {
  issues: SpecLintIssue[]
}

export function lintSpecV0 (spec: SpecV0): SpecLintResult {
  const issues: SpecLintIssue[] = []

  for (const [entityName, entity] of Object.entries(spec.entities ?? {})) {
    const states = new Set(entity.states ?? [])
    const allStates = Array.from(states)
    const initial = entity.initial
    const commands = entity.commands ?? {}
    const reducers = entity.reducers ?? {}

    type CmdMeta = {
      name: string
      guardStates: Set<string> | null
      targetStates: Set<string>
    }
    const cmdMeta: CmdMeta[] = []

    for (const [cmdName, cmdAny] of Object.entries(commands)) {
      const cmd = cmdAny as any
      const guardStates = extractGuardStates(cmd.when)

      if (guardStates == null) {
        issues.push({
          code: "ANTI_PATTERN_UNSCOPED_COMMAND",
          path: `entities.${entityName}.commands.${cmdName}.when`,
          message: "command is not state-scoped; prefer explicit state predicates in guards",
          severity: "warning",
        })
      }

      if (Array.isArray(cmd.emit) && cmd.emit.length > 1) {
        issues.push({
          code: "ANTI_PATTERN_MULTI_EMIT",
          path: `entities.${entityName}.commands.${cmdName}.emit`,
          message: "command emits multiple events; prefer one semantic event per command in v0",
          severity: "warning",
        })
      }

      const targetStates = new Set<string>()
      for (const em of (cmd.emit ?? []) as any[]) {
        const eventType = String(em?.type ?? "")
        const ops = reducers[eventType] ?? []
        let setStateCount = 0
        for (const opAny of ops as any[]) {
          const op = opAny as any
          if (!op || typeof op !== "object" || Array.isArray(op)) continue
          const tag = Object.keys(op)[0]
          if (tag !== "set_state") continue

          setStateCount++
          const next = readSetStateLiteral(op[tag])
          if (next && states.has(next)) targetStates.add(next)
        }

        if (setStateCount > 1) {
          issues.push({
            code: "ANTI_PATTERN_MULTIPLE_STATE_WRITES",
            path: `entities.${entityName}.reducers.${eventType}`,
            message: "reducer writes state multiple times for one event; this is hard to reason about",
            severity: "warning",
          })
        }
      }

      cmdMeta.push({ name: cmdName, guardStates, targetStates })
    }

    // Build a conservative transition graph from command guards + reducer state writes.
    const edges = new Map<string, Set<string>>()
    for (const s of allStates) edges.set(s, new Set())
    for (const c of cmdMeta) {
      const fromStates = c.guardStates == null ? allStates : Array.from(c.guardStates).filter((s) => states.has(s))
      for (const from of fromStates) {
        if (c.targetStates.size === 0) {
          edges.get(from)?.add(from)
        } else {
          for (const to of c.targetStates) edges.get(from)?.add(to)
        }
      }
    }

    const reachable = new Set<string>()
    if (states.has(initial)) {
      const queue: string[] = [initial]
      reachable.add(initial)
      while (queue.length) {
        const cur = queue.shift()!
        for (const nxt of edges.get(cur) ?? []) {
          if (reachable.has(nxt)) continue
          reachable.add(nxt)
          queue.push(nxt)
        }
      }
    }

    for (const s of allStates) {
      if (reachable.has(s)) continue
      issues.push({
        code: "UNREACHABLE_STATE",
        path: `entities.${entityName}.states`,
        message: `state '${s}' is unreachable from initial state '${initial}'`,
        severity: "warning",
      })
    }

    for (const c of cmdMeta) {
      const fromStates = c.guardStates == null ? allStates : Array.from(c.guardStates).filter((s) => states.has(s))
      const enabled = fromStates.some((s) => reachable.has(s))
      if (enabled) continue
      issues.push({
        code: "DEAD_COMMAND",
        path: `entities.${entityName}.commands.${c.name}`,
        message: "command is dead; no reachable state can satisfy its guard",
        severity: "warning",
      })
    }
  }

  return { issues }
}

function extractGuardStates (when: any): Set<string> | null {
  if (when == null) return null
  if (!when || typeof when !== "object" || Array.isArray(when)) return null

  if (typeof when.state_is === "string") return new Set([String(when.state_is)])

  if (Array.isArray(when.all)) {
    let acc: Set<string> | null = null
    for (const part of when.all) {
      const p = extractGuardStates(part)
      if (p == null) continue
      if (acc == null) {
        acc = new Set(p)
      } else {
        acc = intersect(acc, p)
      }
    }
    return acc
  }

  if (Array.isArray(when.any)) {
    const acc = new Set<string>()
    let sawKnown = false
    for (const part of when.any) {
      const p = extractGuardStates(part)
      if (p == null) continue
      sawKnown = true
      for (const s of p) acc.add(s)
    }
    return sawKnown ? acc : null
  }

  return null
}

function readSetStateLiteral (body: any): string | null {
  if (typeof body === "string") return body
  const lit = body?.expr?.lit
  if (lit && typeof lit.string === "string") return String(lit.string)
  return null
}

function intersect (a: Set<string>, b: Set<string>): Set<string> {
  const out = new Set<string>()
  for (const x of a) if (b.has(x)) out.add(x)
  return out
}
