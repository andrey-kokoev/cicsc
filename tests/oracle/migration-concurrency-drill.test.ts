import { describe, it } from "node:test"
import assert from "node:assert/strict"

class MigrationGate {
  private paused = false
  private schemaVersion = 1

  pauseForMigration() {
    this.paused = true
  }

  migrate() {
    if (!this.paused) {
      throw new Error("migrate_requires_pause")
    }
    this.schemaVersion += 1
  }

  resume() {
    this.paused = false
  }

  executeCommand(commandId: string): { ok: boolean; reason?: string; version: number; commandId: string } {
    if (this.paused) {
      return { ok: false, reason: "migration_paused", version: this.schemaVersion, commandId }
    }
    return { ok: true, version: this.schemaVersion, commandId }
  }
}

describe("phase6 migration-under-concurrency drill", () => {
  it("enforces pause/migrate/resume behavior under concurrent command attempts", async () => {
    const gate = new MigrationGate()

    const prePause = gate.executeCommand("cmd-pre")
    assert.equal(prePause.ok, true)
    assert.equal(prePause.version, 1)

    gate.pauseForMigration()

    const duringPauseA = Promise.resolve(gate.executeCommand("cmd-during-a"))
    const duringPauseB = Promise.resolve(gate.executeCommand("cmd-during-b"))

    gate.migrate()
    gate.resume()

    const postResume = gate.executeCommand("cmd-post")

    const pausedResults = await Promise.all([duringPauseA, duringPauseB])
    for (const r of pausedResults) {
      assert.equal(r.ok, false)
      assert.equal(r.reason, "migration_paused")
      assert.equal(r.version, 1)
    }

    assert.equal(postResume.ok, true)
    assert.equal(postResume.version, 2)
  })
})
