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
  const viewIndexes = genViewIndexes(ir, v)
  const versions = genTenantVersions()
  const receipts = genCommandReceipts()
  const sla = genSlaStatus()

  const sql = [versions, receipts, events, snapshots, viewIndexes, sla].join("\n\n")
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

function genViewIndexes (ir: CoreIrV0, version: number): string {
  const fields = collectIndexedFieldsFromViews(ir)
    .filter((f) => f !== "attrs_json" && f !== "state")

  if (fields.length === 0) return ""

  return fields
    .map((f) => {
      const safe = sanitizeIndexToken(f)
      return `
CREATE INDEX IF NOT EXISTS idx_snapshots_v${version}_view_${safe}
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
