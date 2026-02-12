import type { BoolQueryConstraintV0, ConstraintSpecV0, CoreIrV0, SnapshotConstraintV0 } from "../ir/types"
import { interpretQuery, type QueryContext, type SnapRow, type SlaRow } from "../query/interpret"
import { evalExpr, type VmEnv, type VmIntrinsics, type Value } from "../vm/eval"

export type ConstraintViolation = {
  constraint_id: string
  kind: "snapshot" | "bool_query"
  on_type: string
  message: string
  sample?: Record<string, Value>
}

export type ConstraintRunInputs = {
  ir: CoreIrV0
  intrinsics: VmIntrinsics
  policies?: VmEnv["policies"]

  // snapshot materialization, for Query sources
  snapshotsByType: (typeName: string) => SnapRow[]
  slaStatus: (name: string, onType: string) => SlaRow[]

  // evaluation context
  now: number
  actor: string
}

export function runAllConstraints (inputs: ConstraintRunInputs): ConstraintViolation[] {
  const out: ConstraintViolation[] = []
  const constraints = inputs.ir.constraints ?? {}

  for (const [id, c] of Object.entries(constraints)) {
    const cs = c as ConstraintSpecV0
    if (cs.kind === "snapshot") out.push(...runSnapshotConstraint(id, cs as SnapshotConstraintV0, inputs))
    else if (cs.kind === "bool_query") out.push(...runBoolQueryConstraint(id, cs as BoolQueryConstraintV0, inputs))
    else out.push({ constraint_id: id, kind: "snapshot", on_type: (cs as any).on_type ?? "?", message: "unknown constraint kind" })
  }

  return out
}

function runSnapshotConstraint (id: string, c: SnapshotConstraintV0, inputs: ConstraintRunInputs): ConstraintViolation[] {
  const rows = inputs.snapshotsByType(c.on_type)
  const viols: ConstraintViolation[] = []

  for (const row of rows) {
    const env: VmEnv = {
      now: inputs.now,
      actor: inputs.actor,
      state: typeof row["state"] === "string" ? (row["state"] as string) : "",
      input: {},
      attrs: extractAttrs(row),
      row,
      arg: {},
      intrinsics: inputs.intrinsics,
      policies: inputs.policies,
    }

    const ok = toBool(evalExpr(c.expr, env))
    if (!ok) {
      viols.push({
        constraint_id: id,
        kind: "snapshot",
        on_type: c.on_type,
        message: "snapshot constraint violated",
        sample: { entity_id: row["entity_id"] ?? null, state: row["state"] ?? null },
      })
    }
  }

  return viols
}

function runBoolQueryConstraint (id: string, c: BoolQueryConstraintV0, inputs: ConstraintRunInputs): ConstraintViolation[] {
  const ctx: QueryContext = {
    now: inputs.now,
    actor: inputs.actor,
    snap: (t) => inputs.snapshotsByType(t),
    sla_status: (name, onType) => inputs.slaStatus(name, onType),
    baseEnv: {
      now: inputs.now,
      actor: inputs.actor,
      state: "",
      input: {},
      attrs: {},
      row: {},
      arg: {},
      intrinsics: inputs.intrinsics,
      policies: inputs.policies,
    } as any,
  }

  const { rows, rows_count } = interpretQuery(c.query, ctx)

  const env: VmEnv = {
    now: inputs.now,
    actor: inputs.actor,
    state: "",
    input: {},
    attrs: {},
    row: {},
    arg: {},
    rows_count,
    agg: {},
    intrinsics: inputs.intrinsics,
    policies: inputs.policies,
  }

  const ok = toBool(evalExpr(c.assert, env))
  if (ok) return []

  return [
    {
      constraint_id: id,
      kind: "bool_query",
      on_type: c.on_type,
      message: "bool_query constraint violated",
      sample: { rows_count, first_row: (rows[0] as any) ?? null },
    },
  ]
}

function extractAttrs (row: Record<string, Value>): Record<string, Value> {
  // Convention: attrs may be present as `attrs.<k>` or as flattened keys.
  // Keep both so replay-projected rows and query-projected rows share behavior.
  const out: Record<string, Value> = {}
  const core = new Set(["entity_type", "entity_id", "state", "updated_ts", "attrs_json"])
  for (const [k, v] of Object.entries(row)) {
    if (k.startsWith("attrs.")) out[k.slice("attrs.".length)] = v
    else if (!core.has(k)) out[k] = v
  }
  return out
}

function toBool (v: Value): boolean {
  if (v === null) return false
  if (typeof v === "boolean") return v
  if (typeof v === "number") return v !== 0
  if (typeof v === "string") return v.length > 0
  if (Array.isArray(v)) return v.length > 0
  return Object.keys(v).length > 0
}
