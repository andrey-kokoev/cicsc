import type { SpecV0 } from "./ast"

export function parseSpecV0 (input: string | unknown): SpecV0 {
  const raw = typeof input === "string" ? parseString(input) : input
  if (!raw || typeof raw !== "object" || Array.isArray(raw)) {
    throw new Error("spec must be an object")
  }

  const o = raw as any
  if (o.types) {
    throw new Error("spec must use DSL shape (entities), not IR shape (types)")
  }
  if (!o.entities || typeof o.entities !== "object" || Array.isArray(o.entities)) {
    throw new Error("spec.entities is required")
  }

  const version = Number(o.version ?? 0)
  if (version !== 0) throw new Error("spec.version must be 0")

  return o as SpecV0
}

function parseString (s: string): unknown {
  const text = s.trim()
  if (!text) throw new Error("empty spec input")

  try {
    return JSON.parse(text)
  } catch {
    // Optional YAML parser support if dependency is installed.
    try {
      // eslint-disable-next-line @typescript-eslint/no-var-requires
      const yaml = require("yaml")
      return yaml.parse(text)
    } catch {
      throw new Error("spec string must be JSON, or install 'yaml' dependency for YAML input")
    }
  }
}
