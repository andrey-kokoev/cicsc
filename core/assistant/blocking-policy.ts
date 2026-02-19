export type BlockingIssue = {
  code: string
  path: string
  severity: "error" | "warning"
  message: string
}

export function normalizeBlockingIssues (raw: unknown): BlockingIssue[] {
  if (!Array.isArray(raw)) return []
  const out: BlockingIssue[] = []
  for (let i = 0; i < raw.length; i++) {
    const issue = raw[i]
    if (issue && typeof issue === "object" && !Array.isArray(issue)) {
      const o = issue as any
      out.push({
        code: typeof o.code === "string" ? o.code : "BLOCKING_ISSUE",
        path: typeof o.path === "string" ? o.path : `$.blocking_issues[${i}]`,
        severity: o.severity === "warning" ? "warning" : "error",
        message: typeof o.message === "string" ? o.message : "blocking issue",
      })
    } else if (typeof issue === "string") {
      out.push({
        code: "BLOCKING_ISSUE",
        path: `$.blocking_issues[${i}]`,
        severity: "error",
        message: issue,
      })
    }
  }
  return out
}

export function isDeployable (issues: BlockingIssue[]): boolean {
  return issues.every((i) => i.severity !== "error")
}
