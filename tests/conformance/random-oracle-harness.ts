// /tests/conformance/random-oracle-harness.ts

import assert from "node:assert/strict"

import { interpretQuery } from "../../core/query/interpret"
import { lowerQueryToSql } from "../../adapters/sqlite/src/lower/query-to-sql"
import { installSqliteSchemaV0, openSqliteMemory, runLoweredQueryPlan, upsertSnapshot } from "../harness/sqlite-memory"

function stableNormalize (v: any): any {
  if (v === null || typeof v !== "object") return v
  if (Array.isArray(v)) return v.map(stableNormalize)
  const out: any = {}
  for (const k of Object.keys(v).sort()) out[k] = stableNormalize(v[k])
  return out
}

function canonRows (rows: any[]): any[] {
  const norm = rows.map(stableNormalize)
  norm.sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)))
  return norm
}

function oracleCtx (snapRows: any[]) {
  return {
    now: 1,
    actor: "u",
    snap: () => snapRows,
    sla_status: () => [],
    baseEnv: {
      now: 1,
      actor: "u",
      state: "",
      input: {},
      attrs: {},
      arg: {},
      intrinsics: {
        has_role: () => false,
        role_of: () => "agent",
        auth_ok: () => true,
        constraint: () => true,
        len: () => 0,
        str: (v: any) => (v === null ? null : String(v)),
        int: (v: any) => (typeof v === "number" ? Math.trunc(v) : null),
        float: (v: any) => (typeof v === "number" ? v : null),
      },
    },
  }
}

export function assertSqliteOracleParity (query: any, snapRows: any[]) {
  const db = openSqliteMemory()
  try {
    installSqliteSchemaV0(db)
    for (const row of snapRows) {
      upsertSnapshot(db, {
        tenant_id: "t",
        entity_type: "Ticket",
        entity_id: row.entity_id,
        state: row.state,
        attrs: {},
        updated_ts: 1,
        severity_i: row.severity_i ?? null,
        created_at: row.created_at ?? null,
      })
    }

    const plan = lowerQueryToSql(query, { version: 0, tenant_id: "t" })
    const sqlRows = runLoweredQueryPlan(db, { tenant_id: "t", query, plan })
    const sqlProjected = sqlRows.map((r: any) => ({
      id: r.id,
      state: r.state,
      sev: r.sev,
    }))

    const oracle = interpretQuery(query, oracleCtx(snapRows) as any)
    assert.deepEqual(canonRows(sqlProjected), canonRows(oracle.rows))
  } finally {
    db.close()
  }
}
