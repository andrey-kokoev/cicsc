// /runtime/db/install-schema.ts

type D1Database = {
  exec (sql: string): Promise<any>
}

export async function installSchemaV0 (db: D1Database): Promise<void> {
  // D1 supports executing multiple statements via exec (it splits on semicolons).
  // Keep it idempotent with IF NOT EXISTS.
  const sql = `
    CREATE TABLE IF NOT EXISTS tenant_versions (
      tenant_id      TEXT PRIMARY KEY,
      active_version INTEGER NOT NULL
    );

    CREATE TABLE IF NOT EXISTS command_receipts (
      tenant_id    TEXT NOT NULL,
      command_id   TEXT NOT NULL,
      entity_type  TEXT NOT NULL,
      entity_id    TEXT NOT NULL,
      result_json  TEXT NOT NULL,
      ts           INTEGER NOT NULL,
      PRIMARY KEY (tenant_id, command_id)
    );

    CREATE TABLE IF NOT EXISTS events_v0 (
      tenant_id   TEXT NOT NULL,
      entity_type TEXT NOT NULL,
      entity_id   TEXT NOT NULL,
      seq         INTEGER NOT NULL,
      event_type  TEXT NOT NULL,
      payload_json TEXT NOT NULL,
      ts          INTEGER NOT NULL,
      actor_id    TEXT NOT NULL,
      PRIMARY KEY (tenant_id, entity_type, entity_id, seq)
    );

    CREATE INDEX IF NOT EXISTS idx_events_stream_v0
      ON events_v0(tenant_id, entity_type, entity_id, ts);

    CREATE INDEX IF NOT EXISTS idx_events_type_time_v0
      ON events_v0(tenant_id, entity_type, event_type, ts);

    CREATE TABLE IF NOT EXISTS snapshots_v0 (
      tenant_id   TEXT NOT NULL,
      entity_type TEXT NOT NULL,
      entity_id   TEXT NOT NULL,
      state       TEXT NOT NULL,
      attrs_json  TEXT NOT NULL,
      updated_ts  INTEGER NOT NULL,
      -- example shadow columns for ticketing.v0 bundle; safe even if unused by other bundles
      severity_i  INTEGER,
      created_at  INTEGER,
      PRIMARY KEY (tenant_id, entity_type, entity_id)
    );

    CREATE INDEX IF NOT EXISTS idx_snapshots_state_v0
      ON snapshots_v0(tenant_id, entity_type, state);

    CREATE TABLE IF NOT EXISTS sla_status (
      tenant_id   TEXT NOT NULL,
      name        TEXT NOT NULL,
      entity_type TEXT NOT NULL,
      entity_id   TEXT NOT NULL,
      start_ts    INTEGER,
      stop_ts     INTEGER,
      deadline_ts INTEGER,
      breached    INTEGER NOT NULL,
      updated_ts  INTEGER NOT NULL,
      PRIMARY KEY (tenant_id, name, entity_type, entity_id)
    );

    CREATE INDEX IF NOT EXISTS idx_sla_breached
      ON sla_status(tenant_id, name, breached, deadline_ts);
  `

  await db.exec(sql)
}
