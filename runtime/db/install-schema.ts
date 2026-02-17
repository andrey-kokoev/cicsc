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
      command_id  TEXT,
      PRIMARY KEY (tenant_id, entity_type, entity_id, seq)
    );

    CREATE INDEX IF NOT EXISTS idx_events_stream_v0
      ON events_v0(tenant_id, entity_type, entity_id, ts);

    CREATE INDEX IF NOT EXISTS idx_events_command_v0
      ON events_v0(tenant_id, command_id, ts);

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

    CREATE TABLE IF NOT EXISTS idempotency_keys (
      tenant_id    TEXT NOT NULL,
      key          TEXT NOT NULL,
      queue_name   TEXT NOT NULL,
      processed_at INTEGER NOT NULL,
      result_json  TEXT,
      PRIMARY KEY (tenant_id, key, queue_name)
    );

    CREATE TABLE IF NOT EXISTS scheduled_jobs (
      id            TEXT PRIMARY KEY,
      tenant_id     TEXT NOT NULL,
      schedule_name TEXT NOT NULL,
      scheduled_at  INTEGER NOT NULL,
      job_data      TEXT NOT NULL,
      status        TEXT NOT NULL DEFAULT 'pending',
      result_json   TEXT,
      created_at    INTEGER NOT NULL,
      updated_at    INTEGER NOT NULL
    );

    CREATE INDEX IF NOT EXISTS idx_scheduled_jobs_tenant_status
      ON scheduled_jobs(tenant_id, status, scheduled_at);

    CREATE INDEX IF NOT EXISTS idx_scheduled_jobs_schedule
      ON scheduled_jobs(schedule_name, status, scheduled_at);

    CREATE TABLE IF NOT EXISTS workflow_instances (
      id            TEXT PRIMARY KEY,
      tenant_id     TEXT NOT NULL,
      workflow_name TEXT NOT NULL,
      state         TEXT NOT NULL DEFAULT 'pending',
      current_step  TEXT,
      data          TEXT NOT NULL,
      created_at    INTEGER NOT NULL,
      updated_at    INTEGER NOT NULL
    );

    CREATE INDEX IF NOT EXISTS idx_workflow_instances_tenant_state
      ON workflow_instances(tenant_id, workflow_name, state);

    CREATE INDEX IF NOT EXISTS idx_workflow_instances_current_step
      ON workflow_instances(current_step);
  `

  await db.exec(sql)
}
