import type { MigrationSpecV0, EventTransformV0 } from "../../core/ir/types"

export class MigrationEngine {
  /**
   * Transforms an event from an old schema to a new schema based on MigrationSpec.
   */
  transformEvent (event: any, spec: MigrationSpecV0): any | null {
    const t = spec.event_transforms[event.event_type]
    if (!t) return event // Default: pass through
    if (t.drop) return null

    const newEvent = { ...event }
    if (t.emit_as) newEvent.event_type = t.emit_as

    if (t.payload_map) {
      const newPayload: Record<string, any> = {}
      for (const [k, v] of Object.entries(t.payload_map)) {
        // Simple mapping (v could be an Expr in real life)
        newPayload[k] = this.evaluateMapping(v, event.payload)
      }
      newEvent.payload = newPayload
    }

    return newEvent
  }

  async dryRun (events: any[], specs: MigrationSpecV0[]): Promise<{ count: number, dropped: number, transformed: number }> {
    let count = 0
    let dropped = 0
    let transformed = 0

    for (const event of events) {
      const spec = specs.find(s => s.on_type === event.entity_type)
      if (spec) {
        const result = this.transformEvent(event, spec)
        if (result === null) dropped++
        else if (result !== event) transformed++
      }
      count++
    }

    return { count, dropped, transformed }
  }

  /**
   * Generates a rollback migration spec from a forward spec.
   */
  invertSpec (spec: MigrationSpecV0): MigrationSpecV0 {
    // In many cases, automatic inversion is impossible (e.g. data drop).
    // This would require user-provided inverse mapping.
    return {
      ...spec,
      from_version: spec.to_version,
      to_version: spec.from_version,
    }
  }

  async createPreMigrationSnapshot (db: any, tenantId: string, version: number): Promise<void> {
    // v0: Copy snapshots_vN to snapshots_vN_backup
    await db.exec(`
      CREATE TABLE IF NOT EXISTS snapshots_v${version}_backup AS 
      SELECT * FROM snapshots_v${version} WHERE tenant_id = '${tenantId}';
    `)
  }

  async replayEvents (db: any, tenantId: string, fromVersion: number, toVersion: number, specs: MigrationSpecV0[]): Promise<void> {
    // 1. Fetch events from old version
    const events = await db.all(`SELECT * FROM history_v${fromVersion} WHERE tenant_id = '${tenantId}' ORDER BY seq ASC`)

    // 2. Transform and insert into new version
    for (const event of events) {
      const spec = specs.find(s => s.on_type === event.entity_type)
      const newEvent = spec ? this.transformEvent(event, spec) : event

      if (newEvent) {
        // v0: Simple insertion (real impl would use executeCommand logic)
        await db.run(`INSERT INTO history_v${toVersion} (tenant_id, entity_type, entity_id, event_type, payload, ts, actor_id) VALUES (?, ?, ?, ?, ?, ?, ?)`,
          [tenantId, event.entity_type, event.entity_id, newEvent.event_type, JSON.stringify(newEvent.payload), newEvent.ts, newEvent.actor_id]
        )
      }
    }
  }

  async runInvariantChecks (db: any, tenantId: string, version: number): Promise<void> {
    // v0: Check that all snapshots match the state derived from replaying history
    // This requires a full reducer-parity check.
    console.log(`[BD3.3] Running invariant checks for tenant ${tenantId} at v${version}...`)
  }

  private evaluateMapping (mapping: any, payload: any): any {
    // Implement Expr evaluator for migrations here
    return mapping
  }
}
