// /tests/conformance/sqlite-random-vs-oracle.test.ts
// Phase 4: Random differential testing with deterministic replay support (P4.2.3)

import { describe, it } from "node:test"

import { generateCases } from "./random-query-generator"
import { assertSqliteOracleParity, replayFromArtifactFile } from "./random-oracle-harness"

// Support replaying from artifact for debugging (P4.2.3)
const replayArtifact = process.env["CICSC_REPLAY_ARTIFACT"]

if (replayArtifact) {
  describe("conformance: replay from artifact (P4.2.3)", () => {
    it(`replays artifact: ${replayArtifact}`, () => {
      const result = replayFromArtifactFile(replayArtifact)
      if (!result.success) {
        throw new Error(`Replay failed: ${result.error}`)
      }
    })
  })
} else {
  describe("conformance: sqlite random generated vs oracle", () => {
    it("matches oracle on generated query/snapshot cases", () => {
      const caseCount = parseInt(process.env["CICSC_RANDOM_CASE_COUNT"] || "25", 10)
      const seedBase = parseInt(process.env["CICSC_RANDOM_SEED_BASE"] || "2000", 10)
      const cases = generateCases(caseCount, seedBase)
      
      const failures: Array<{ seed: number; error: string; artifactPath?: string | null }> = []
      
      for (const c of cases) {
        try {
          assertSqliteOracleParity(c.query, c.snapRows, c.seed)
        } catch (err: any) {
          failures.push({
            seed: c.seed,
            error: err?.message ?? String(err),
          })
        }
      }
      
      if (failures.length > 0) {
        const summary = failures.map(f => `  seed ${f.seed}: ${f.error.split('\n')[0]}`).join('\n')
        throw new Error(
          `${failures.length}/${cases.length} conformance cases failed:\n${summary}\n\n` +
          `Replay artifacts written to: ${process.env["CICSC_CONFORMANCE_ARTIFACT_DIR"] || "./test-artifacts/conformance"}\n` +
          `To replay a specific case: CICSC_REPLAY_ARTIFACT=<path> npm test`
        )
      }
    })
  })
}
