// /tests/conformance/random-query-generator.ts

type Rng = () => number

function mkRng (seed: number): Rng {
  let s = seed >>> 0
  return () => {
    s = (1664525 * s + 1013904223) >>> 0
    return s / 0x100000000
  }
}

function pick<T> (rng: Rng, xs: T[]): T {
  return xs[Math.floor(rng() * xs.length)] as T
}

export type GeneratedCase = {
  seed: number
  query: any
  snapRows: any[]
}

export function generateCase (seed: number): GeneratedCase {
  const rng = mkRng(seed)
  const states = ["new", "triage", "done"]
  const n = 1 + Math.floor(rng() * 8)
  const snapRows = Array.from({ length: n }, (_, i) => ({
    entity_id: `e${i}`,
    state: pick(rng, states),
    severity_i: Math.floor(rng() * 5),
    created_at: i + 1,
  }))

  const maybeFilter = rng() > 0.35
  const maybeOrder = rng() > 0.45
  const maybeLimit = rng() > 0.55

  const pipeline: any[] = []
  if (maybeFilter) {
    pipeline.push({
      filter: {
        eq: [
          { var: { row: { field: "state" } } },
          { lit: { string: pick(rng, states) } },
        ],
      },
    })
  }
  if (maybeOrder) {
    pipeline.push({
      order_by: [{ expr: { var: { row: { field: "severity_i" } } }, dir: "desc" }],
    })
  }
  pipeline.push({
    project: {
      fields: [
        { name: "id", expr: { var: { row: { field: "entity_id" } } } },
        { name: "state", expr: { var: { row: { field: "state" } } } },
        { name: "sev", expr: { var: { row: { field: "severity_i" } } } },
      ],
    },
  })
  if (maybeLimit) {
    pipeline.push({ limit: 1 + Math.floor(rng() * n) })
  }

  return {
    seed,
    query: {
      source: { snap: { type: "Ticket" } },
      pipeline,
    },
    snapRows,
  }
}

export function generateCases (count: number, seedBase = 1000): GeneratedCase[] {
  return Array.from({ length: count }, (_, i) => generateCase(seedBase + i))
}
