CREATE TABLE IF NOT EXISTS tenant_versions (
  tenant_id      TEXT PRIMARY KEY,
  active_version INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS command_receipts (
  tenant_id    TEXT NOT NULL,
  command_id   TEXT NOT NULL,
  entity_type  TEXT NOT NULL,
  entity_id    TEXT NOT NULL,
  result_json  JSONB NOT NULL,
  ts           BIGINT NOT NULL,
  PRIMARY KEY (tenant_id, command_id)
);

CREATE TABLE IF NOT EXISTS events_v0 (
  tenant_id   TEXT NOT NULL,
  entity_type TEXT NOT NULL,
  entity_id   TEXT NOT NULL,
  seq         BIGINT NOT NULL,
  event_type  TEXT NOT NULL,
  payload     JSONB NOT NULL,
  ts          BIGINT NOT NULL,
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
  attrs       JSONB NOT NULL,
  updated_ts  BIGINT NOT NULL,
  PRIMARY KEY (tenant_id, entity_type, entity_id)
);

CREATE INDEX IF NOT EXISTS idx_snapshots_state_v0
  ON snapshots_v0(tenant_id, entity_type, state);

CREATE TABLE IF NOT EXISTS sla_status (
  tenant_id   TEXT NOT NULL,
  name        TEXT NOT NULL,
  entity_type TEXT NOT NULL,
  entity_id   TEXT NOT NULL,
  start_ts    BIGINT,
  stop_ts     BIGINT,
  deadline_ts BIGINT,
  breached    BOOLEAN NOT NULL,
  updated_ts  BIGINT NOT NULL,
  PRIMARY KEY (tenant_id, name, entity_type, entity_id)
);

CREATE INDEX IF NOT EXISTS idx_sla_breached
  ON sla_status(tenant_id, name, breached, deadline_ts);
