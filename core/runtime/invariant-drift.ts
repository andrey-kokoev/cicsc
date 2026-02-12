import type { VerifyReport } from "./verify"

export type InvariantDrift = {
  detected: boolean
  from_version?: number
  to_version?: number
  newly_violated: string[]
  resolved: string[]
}

export function detectInvariantDrift (params: {
  baseline: VerifyReport
  candidate: VerifyReport
}): InvariantDrift {
  const a = keySet(params.baseline)
  const b = keySet(params.candidate)

  const newly_violated: string[] = []
  const resolved: string[] = []

  for (const k of b) if (!a.has(k)) newly_violated.push(k)
  for (const k of a) if (!b.has(k)) resolved.push(k)

  newly_violated.sort()
  resolved.sort()

  return {
    detected: newly_violated.length > 0,
    from_version: params.baseline.version_stamp?.active_version,
    to_version: params.candidate.version_stamp?.active_version,
    newly_violated,
    resolved,
  }
}

function keySet (r: VerifyReport): Set<string> {
  const out = new Set<string>()
  for (const v of r.violations ?? []) {
    out.add(`${v.constraint_id}|${v.kind}|${v.on_type}|${v.message}`)
  }
  return out
}
