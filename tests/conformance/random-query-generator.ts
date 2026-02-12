// /tests/conformance/random-query-generator.ts
// Phase 4: Deterministic seed replay artifact support (P4.2.3)

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

/** Replay artifact for deterministic failure reproduction (P4.2.3) */
export type ReplayArtifact = {
  version: "cicsc/conformance-replay-v1"
  generatedAt: string
  seed: number
  query: any
  snapRows: any[]
  metadata: {
    generatorVersion: string
    schemaType: string
  }
}

/** Create a replay artifact from a generated case for deterministic reproduction */
export function toReplayArtifact (
  generatedCase: GeneratedCase,
  schemaType = "Ticket"
): ReplayArtifact {
  return {
    version: "cicsc/conformance-replay-v1",
    generatedAt: new Date().toISOString(),
    seed: generatedCase.seed,
    query: generatedCase.query,
    snapRows: generatedCase.snapRows,
    metadata: {
      generatorVersion: "phase4-v1",
      schemaType,
    },
  }
}

/** Serialize artifact to JSON string for file storage */
export function serializeReplayArtifact (artifact: ReplayArtifact): string {
  return JSON.stringify(artifact, null, 2)
}

/** Deserialize artifact from JSON string */
export function deserializeReplayArtifact (json: string): ReplayArtifact {
  const parsed = JSON.parse(json)
  if (parsed.version !== "cicsc/conformance-replay-v1") {
    throw new Error(`Unsupported replay artifact version: ${parsed.version}`)
  }
  return parsed as ReplayArtifact
}

/** Regenerate a case from an artifact for exact replay */
export function regenerateFromArtifact (artifact: ReplayArtifact): GeneratedCase {
  // Verify reproducibility by regenerating from seed
  const regenerated = generateCase(artifact.seed)
  
  // Validate that regeneration matches stored artifact
  const queryMatch = JSON.stringify(regenerated.query) === JSON.stringify(artifact.query)
  const snapMatch = JSON.stringify(regenerated.snapRows) === JSON.stringify(artifact.snapRows)
  
  if (!queryMatch || !snapMatch) {
    throw new Error(
      `Replay artifact seed ${artifact.seed} does not reproduce identical case. ` +
      `Query match: ${queryMatch}, Snap match: ${snapMatch}. ` +
      `Generator version mismatch or non-deterministic generation detected.`
    )
  }
  
  return regenerated
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
