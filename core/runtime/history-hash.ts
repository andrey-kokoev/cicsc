import { createHash } from "node:crypto"
import type { Event } from "./replay"

export function hashEventHistory (events: Event[]): string {
  const normalized = [...events]
    .sort((a, b) =>
      cmp(a.tenant_id, b.tenant_id) ||
      cmp(a.entity_type, b.entity_type) ||
      cmp(a.entity_id, b.entity_id) ||
      a.seq - b.seq ||
      a.ts - b.ts
    )
    .map((e) => ({
      tenant_id: e.tenant_id,
      entity_type: e.entity_type,
      entity_id: e.entity_id,
      seq: e.seq,
      event_type: e.event_type,
      payload: e.payload,
      ts: e.ts,
      actor_id: e.actor_id,
    }))

  return sha256(stableStringify(normalized))
}

export function hashSnapshots (rows: Array<Record<string, unknown>>): string {
  const normalized = [...rows]
    .map((r) => normalizeObject(r))
    .sort((a, b) => cmp(stableStringify(a), stableStringify(b)))
  return sha256(stableStringify(normalized))
}

export function hashTenantState (params: {
  events: Event[]
  snapshots: Array<Record<string, unknown>>
}): { events_hash: string; snapshots_hash: string; combined_hash: string } {
  const events_hash = hashEventHistory(params.events)
  const snapshots_hash = hashSnapshots(params.snapshots)
  const combined_hash = sha256(`${events_hash}:${snapshots_hash}`)
  return { events_hash, snapshots_hash, combined_hash }
}

function sha256 (s: string): string {
  return createHash("sha256").update(s).digest("hex")
}

function cmp (a: string, b: string): number {
  return a < b ? -1 : a > b ? 1 : 0
}

function stableStringify (v: unknown): string {
  if (v === null || typeof v !== "object") return JSON.stringify(v)
  if (Array.isArray(v)) return `[${v.map((x) => stableStringify(x)).join(",")}]`
  const o = v as Record<string, unknown>
  const ks = Object.keys(o).sort()
  return `{${ks.map((k) => `${JSON.stringify(k)}:${stableStringify(o[k])}`).join(",")}}`
}

function normalizeObject (v: Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = {}
  for (const k of Object.keys(v).sort()) out[k] = v[k]
  return out
}
