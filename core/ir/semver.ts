export type SemVer = {
  major: number
  minor: number
  patch: number
}

export function parseSemVer (v: string): SemVer {
  const parts = v.split(".").map(Number)
  if (parts.length !== 3 || parts.some(isNaN)) {
    throw new Error(`Invalid semver: ${v}`)
  }
  return { major: parts[0], minor: parts[1], patch: parts[2] }
}

export function compareSemVer (v1: string, v2: string): number {
  const s1 = parseSemVer(v1)
  const s2 = parseSemVer(v2)

  if (s1.major !== s2.major) return s1.major - s2.major
  if (s1.minor !== s2.minor) return s1.minor - s2.minor
  return s1.patch - s2.patch
}

export function isCompatible (requested: string, available: string): boolean {
  const r = parseSemVer(requested)
  const a = parseSemVer(available)

  // Simple compatibility rule: same major version
  return r.major === a.major && compareSemVer(available, requested) >= 0
}
