import type { CoreIrV0 } from "../../../core/ir/types"

export type SchemaGenOpts = {
  version: number
}

export type SchemaGenOut = {
  sql: string // multi-statement; idempotent
}

export function genSqliteSchemaFromIr (ir: CoreIrV0, opts: SchemaGenOpts): SchemaGenOut {
  const v = opts.version
  const events = genEventsTable(v)
  const snapshots = genSnapshotsTable(ir, v)
  const versions = genTenantVersions()
  const receipts = genCommandReceipts()
  const sla = genSlaStatus()

  const sql = [versions, receipts, events, snapshots, sla].join("\n\n")
  return { sql }
}

function genTenantVersions (): string {
  return `
CREATE TABLE IF NOT EXISTS tenant_versions (
  tenant_id      TEXT PRIMARY KEY,
  active_version INTEGER NOT NULL
);
`.trim()
}

function genCommandReceipts (): string {
  return `
CREATE TABLE IF NOT EXISTS command_receipts (
  tenant_id    TEXT NOT NULL,
  command_id   TEXT NOT NULL,
  entity_type  TEXT NOT NULL,
  entity_id    TEXT NOT NULL,
  result_json  TEXT NOT NULL,
  ts           INTEGER NOT NULL,
  PRIMARY KEY (tenant_id, command_id)
);
`.trim()
}

function genEventsTable (version: number): string {
  return `
CREATE TABLE IF NOT EXISTS events_v${version} (
  tenant_id    TEXT NOT NULL,
  entity_type  TEXT NOT NULL,
  entity_id    TEXT NOT NULL,
  seq          INTEGER NOT NULL,
  event_type   TEXT NOT NULL,
  payload_json TEXT NOT NULL,
  ts           INTEGER NOT NULL,
  actor_id     TEXT NOT NULL,
  PRIMARY KEY (tenant_id, entity_type, entity_id, seq)
);

CREATE INDEX IF NOT EXISTS idx_events_stream_v${version}
  ON events_v${version}(tenant_id, entity_type, entity_id, ts);

CREATE INDEX IF NOT EXISTS idx_events_type_time_v${version}
  ON events_v${version}(tenant_id, entity_type, event_type, ts);
`.trim()
}

function genSnapshotsTable (ir: CoreIrV0, version: number): string {
  // Collect shadow columns across all types; materialize superset in one snapshots table.
  // v0 decision: single snapshots table keyed by (tenant_id, entity_type, entity_id).
  // Shadow columns are nullable; irrelevant columns remain NULL for other types.
  const shadowCols = collectShadowColumns(ir)

  const cols = [
    `tenant_id   TEXT NOT NULL`,
    `entity_type TEXT NOT NULL`,
    `entity_id   TEXT NOT NULL`,
    `state       TEXT NOT NULL`,
    `attrs_json  TEXT NOT NULL`,
    `updated_ts  INTEGER NOT NULL`,
    ...shadowCols.map((c) => `  ${c.name} ${c.sqliteType}`),
    `PRIMARY KEY (tenant_id, entity_type, entity_id)`,
  ]

  const idxState = `
CREATE INDEX IF NOT EXISTS idx_snapshots_state_v${version}
  ON snapshots_v${version}(tenant_id, entity_type, state);
`.trim()

  return `
CREATE TABLE IF NOT EXISTS snapshots_v${version} (
${cols.map((c) => "  " + c).join(",\n")}
);

${idxState}
`.trim()
}

function genSlaStatus (): string {
  return `
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
`.trim()
}

// --------------------
// Shadows
// --------------------

type ShadowCol = { name: string; sqliteType: "INTEGER" | "REAL" | "TEXT" }

function collectShadowColumns (ir: CoreIrV0): ShadowCol[] {
  const map = new Map<string, ShadowCol["sqliteType"]>()

  for (const t of Object.values(ir.types)) {
    const shadows = (t as any).shadows ?? {}
    for (const [name, def] of Object.entries(shadows)) {
      const sqliteType = toSqliteType((def as any).type)
      const prev = map.get(name)
      if (!prev) map.set(name, sqliteType)
      else if (prev !== sqliteType) {
        // If conflict, widen to TEXT (lossy but safe).
        map.set(name, "TEXT")
      }
    }
  }

  return Array.from(map.entries())
    .sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
    .map(([name, sqliteType]) => ({ name: escapeIdent(name), sqliteType }))
}

function toSqliteType (t: string): ShadowCol["sqliteType"] {
  switch (t) {
    case "int":
    case "time":
    case "bool":
      return "INTEGER"
    case "float":
      return "REAL"
    case "string":
    case "enum":
    default:
      return "TEXT"
  }
}

function escapeIdent (name: string): string {
  // Columns: strict; no dots.
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name)) throw new Error(`invalid column ident: ${name}`)
  return `"${name}"`
}
