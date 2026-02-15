import type { CoreIrV0 } from "../../../../core/ir/types"

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
  const viewFields = collectIndexedFieldsFromViews(ir).filter((f) => f !== "attrs_json" && f !== "state")
  const viewIndexes = genSnapshotIndexes(v, "view", viewFields)
  const constraintFields = collectIndexedFieldsFromConstraints(ir)
    .filter((f) => f !== "attrs_json" && f !== "state")
    .filter((f) => !viewFields.includes(f))
  const constraintIndexes = genSnapshotIndexes(v, "constraint", constraintFields)
  const versions = genTenantVersions()
  const receipts = genCommandReceipts()
  const sla = genSlaStatus()
  const queues = genQueues(ir)
  const schedules = genSchedules()
  const workflows = genWorkflows()

  const sql = [versions, receipts, events, snapshots, viewIndexes, constraintIndexes, sla, queues, schedules, workflows].join("\n\n")
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

function genSnapshotIndexes (version: number, kind: "view" | "constraint", fields: string[]): string {
  if (fields.length === 0) return ""

  return fields
    .map((f) => {
      const safe = sanitizeIndexToken(f)
      return `
CREATE INDEX IF NOT EXISTS idx_snapshots_v${version}_${kind}_${safe}
  ON snapshots_v${version}(tenant_id, entity_type, ${escapeIdent(f)});
`.trim()
    })
    .join("\n\n")
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

function collectIndexedFieldsFromViews (ir: CoreIrV0): string[] {
  const out = new Set<string>()
  for (const view of Object.values(ir.views ?? {})) {
    const q: any = (view as any).query
    collectFieldsFromQuery(q, out)
  }
  return Array.from(out).sort()
}

function collectIndexedFieldsFromConstraints (ir: CoreIrV0): string[] {
  const out = new Set<string>()
  for (const c of Object.values(ir.constraints ?? {})) {
    if ((c as any).kind !== "bool_query") continue
    collectFieldsFromQuery((c as any).query, out)
  }
  return Array.from(out).sort()
}

function collectFieldsFromQuery (q: any, out: Set<string>): void {
  if (!q || typeof q !== "object") return
  const pipeline = Array.isArray(q.pipeline) ? q.pipeline : []
  for (const op of pipeline) {
    const tag = soleKey(op)
    const body = (op as any)[tag]
    if (tag === "filter") {
      collectFieldsFromExpr(body, out)
      continue
    }
    if (tag === "order_by") {
      const xs = Array.isArray(body) ? body : []
      for (const k of xs) collectFieldsFromExpr((k as any)?.expr, out)
      continue
    }
  }
}

function collectFieldsFromExpr (expr: any, out: Set<string>): void {
  if (!expr || typeof expr !== "object") return
  const tag = soleKey(expr)
  const body = (expr as any)[tag]

  if (tag === "var") {
    const vTag = soleKey(body)
    const vBody = body[vTag]
    if (vTag === "row") {
      const f = String(vBody?.field ?? "")
      if (f) out.add(f)
    }
    return
  }

  if (tag === "not" || tag === "bool" || tag === "is_null") {
    collectFieldsFromExpr(body, out)
    return
  }

  if (tag === "and" || tag === "or" || tag === "coalesce") {
    for (const x of (Array.isArray(body) ? body : [])) collectFieldsFromExpr(x, out)
    return
  }

  if (tag === "eq" || tag === "ne" || tag === "lt" || tag === "le" || tag === "gt" || tag === "ge" || tag === "add" || tag === "sub" || tag === "mul" || tag === "div" || tag === "time_between") {
    const xs = Array.isArray(body) ? body : []
    for (const x of xs) collectFieldsFromExpr(x, out)
    return
  }

  if (tag === "in") {
    collectFieldsFromExpr(body?.needle, out)
    collectFieldsFromExpr(body?.haystack, out)
    return
  }

  if (tag === "if") {
    collectFieldsFromExpr(body?.cond, out)
    collectFieldsFromExpr(body?.then, out)
    collectFieldsFromExpr(body?.else, out)
    return
  }

  if (tag === "get" || tag === "has") {
    collectFieldsFromExpr(body?.expr, out)
    return
  }

  if (tag === "obj") {
    const fields = body?.fields ?? {}
    for (const v of Object.values(fields)) collectFieldsFromExpr(v, out)
    return
  }

  if (tag === "arr") {
    for (const x of (Array.isArray(body?.items) ? body.items : [])) collectFieldsFromExpr(x, out)
    return
  }

  if (tag === "map_enum") {
    collectFieldsFromExpr(body?.expr, out)
    return
  }

  if (tag === "call") {
    for (const a of (Array.isArray(body?.args) ? body.args : [])) collectFieldsFromExpr(a, out)
    return
  }
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

function sanitizeIndexToken (name: string): string {
  return name.replace(/[^A-Za-z0-9_]/g, "_")
}

function soleKey (o: any): string {
  const ks = Object.keys(o ?? {})
  if (ks.length !== 1) throw new Error("invalid tagged object")
  return ks[0]!
}

function genQueues (ir: CoreIrV0): string {
  const queues = ir.queues ?? {}
  if (Object.keys(queues).length === 0) return ""

  const out: string[] = []

  // Operational idempotency table for queue workers
  out.push(`
CREATE TABLE IF NOT EXISTS idempotency_keys (
  tenant_id    TEXT NOT NULL,
  key          TEXT NOT NULL,
  queue_name   TEXT NOT NULL,
  processed_at INTEGER NOT NULL,
  result_json  TEXT,
  PRIMARY KEY (tenant_id, key, queue_name)
);
`.trim())

  for (const name of Object.keys(queues)) {
    const table = `queue_${name}`
    out.push(`
CREATE TABLE IF NOT EXISTS ${table} (
  tenant_id        TEXT NOT NULL,
  id               TEXT NOT NULL,
  message_json     TEXT NOT NULL,
  idempotency_key  TEXT,
  
  attempts         INTEGER DEFAULT 0,
  visible_after    INTEGER NOT NULL,
  locked_by        TEXT,
  
  created_at       INTEGER NOT NULL,
  updated_at       INTEGER NOT NULL,
  
  PRIMARY KEY (tenant_id, id)
);

CREATE UNIQUE INDEX IF NOT EXISTS idx_${table}_idempotency 
  ON ${table}(tenant_id, idempotency_key) 
  WHERE idempotency_key IS NOT NULL;

CREATE INDEX IF NOT EXISTS idx_${table}_visible 
  ON ${table}(tenant_id, visible_after, created_at);
`.trim())

    // DLQ Table
    const dlqTable = `queue_${name}_dlq`
    out.push(`
CREATE TABLE IF NOT EXISTS ${dlqTable} (
  tenant_id        TEXT NOT NULL,
  id               TEXT NOT NULL,
  message_json     TEXT NOT NULL,
  attempts         INTEGER,
  error            TEXT,
  failed_at        INTEGER NOT NULL,
  
  PRIMARY KEY (tenant_id, id)
);
`.trim())
  }

  function genSchedules (): string {
    return `
CREATE TABLE IF NOT EXISTS scheduled_jobs (
  tenant_id      TEXT NOT NULL,
  id             TEXT NOT NULL,
  schedule_name  TEXT NOT NULL,
  
  trigger_type   TEXT NOT NULL,
  entity_type    TEXT,
  entity_id      TEXT,
  event_type     TEXT,
  
  scheduled_at   INTEGER NOT NULL,
  timezone       TEXT,
  
  command_entity TEXT NOT NULL,
  command_name   TEXT NOT NULL,
  input_json     TEXT NOT NULL,
  
  queue_name     TEXT,
  
  status         TEXT NOT NULL,
  attempts       INTEGER DEFAULT 0,
  last_error     TEXT,
  next_retry_at  INTEGER,
  
  created_at     INTEGER NOT NULL,
  updated_at     INTEGER NOT NULL,
  executed_at    INTEGER,
  
  PRIMARY KEY (tenant_id, id)
);

CREATE INDEX IF NOT EXISTS idx_scheduled_jobs_due
  ON scheduled_jobs(tenant_id, status, scheduled_at)
  WHERE status IN ('pending', 'failed');

CREATE INDEX IF NOT EXISTS idx_scheduled_jobs_entity
  ON scheduled_jobs(tenant_id, entity_type, entity_id)
  WHERE entity_type IS NOT NULL;

CREATE TABLE IF NOT EXISTS cron_schedules (
  tenant_id      TEXT NOT NULL,
  name           TEXT NOT NULL,
  expression     TEXT NOT NULL,
  timezone       TEXT,
  last_run_at    INTEGER,
  next_run_at    INTEGER NOT NULL,
  PRIMARY KEY (tenant_id, name)
);
`.trim()
  }

  function genWorkflows (): string {
    return `
-- Workflow instances track the active state of a saga/workflow
CREATE TABLE IF NOT EXISTS workflow_instances (
  tenant_id       TEXT NOT NULL,
  workflow_id     TEXT NOT NULL,
  workflow_name   TEXT NOT NULL,
  current_step    TEXT NOT NULL,
  status          TEXT NOT NULL, -- 'running', 'waiting', 'completed', 'failed', 'compensated'
  wait_event_type TEXT,          -- for 'wait' steps expecting an event
  context_json    TEXT NOT NULL, -- accumulated inputs/outputs
  history_json    TEXT NOT NULL, -- step history
  next_run_at     INTEGER,       -- for 'wait' steps
  created_ts      INTEGER NOT NULL,
  updated_ts      INTEGER NOT NULL,
  PRIMARY KEY (tenant_id, workflow_id)
);

CREATE INDEX IF NOT EXISTS idx_workflow_instances_polling ON workflow_instances (tenant_id, status, next_run_at) WHERE status IN ('running', 'waiting');

-- Workflow log for auditing and replay
CREATE TABLE IF NOT EXISTS workflow_log (
  tenant_id       TEXT NOT NULL,
  workflow_id     TEXT NOT NULL,
  step_name       TEXT NOT NULL,
  action          TEXT NOT NULL, -- 'start', 'end', 'fail', 'compensate'
  payload_json    TEXT NOT NULL,
  ts              INTEGER NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_workflow_log_id ON workflow_log (tenant_id, workflow_id);

-- Incidents for tracking failures and stuck processes
CREATE TABLE IF NOT EXISTS incidents (
  id              TEXT PRIMARY KEY,
  tenant_id       TEXT NOT NULL,
  source_type     TEXT NOT NULL, -- 'workflow', 'schedule'
  source_id       TEXT NOT NULL,
  incident_type   TEXT NOT NULL, -- 'workflow_stuck', 'schedule_failed', etc.
  message         TEXT NOT NULL,
  status          TEXT NOT NULL, -- 'open', 'resolved', 'ignored'
  context_json    TEXT NOT NULL,
  created_ts      INTEGER NOT NULL
);

CREATE INDEX IF NOT EXISTS idx_incidents_tenant_status ON incidents (tenant_id, status);
`.trim()
  }
