// /tests/conformance/operator-coverage-report.ts
// Phase 4: Operator coverage report for conformance suites (P4.2.5)

import * as fs from "node:fs"
import * as path from "node:path"
import { fileURLToPath } from "node:url"

/** Query operators tracked for coverage */
export type QueryOperator =
  | "source:snap"
  | "source:join"
  | "op:filter"
  | "op:project"
  | "op:order_by"
  | "op:limit"
  | "op:offset"
  | "op:group_by"
  | "op:having"
  | "op:distinct"
  | "op:setOp"

/** Expression operators tracked for coverage */
export type ExprOperator =
  | "expr:eq"
  | "expr:neq"
  | "expr:lt"
  | "expr:lte"
  | "expr:gt"
  | "expr:gte"
  | "expr:and"
  | "expr:or"
  | "expr:not"
  | "expr:add"
  | "expr:sub"
  | "expr:mul"
  | "expr:div"
  | "expr:lit"
  | "expr:var:row"
  | "expr:var:state"
  | "expr:var:input"
  | "expr:get"
  | "expr:has"
  | "expr:coalesce"
  | "expr:if"
  | "expr:in"
  | "expr:exists"
  | "expr:count"
  | "expr:sum"
  | "expr:avg"
  | "expr:min"
  | "expr:max"

/** Coverage entry for an operator */
export type OperatorCoverage = {
  operator: QueryOperator | ExprOperator
  category: "query" | "expr"
  status: "covered" | "partial" | "uncovered" | "deferred"
  testFiles: string[]
  notes?: string
}

/** Full coverage report */
export type CoverageReport = {
  generatedAt: string
  summary: {
    totalOperators: number
    covered: number
    partial: number
    uncovered: number
    deferred: number
    coveragePercent: number
  }
  queryOperators: OperatorCoverage[]
  exprOperators: OperatorCoverage[]
  gaps: Array<{ operator: string; priority: "high" | "medium" | "low"; reason: string }>
}

/** All query operators that should be covered */
const ALL_QUERY_OPERATORS: QueryOperator[] = [
  "source:snap",
  "source:join",
  "op:filter",
  "op:project",
  "op:order_by",
  "op:limit",
  "op:offset",
  "op:group_by",
  "op:having",
  "op:distinct",
  "op:setOp",
]

/** All expression operators that should be covered */
const ALL_EXPR_OPERATORS: ExprOperator[] = [
  "expr:eq",
  "expr:neq",
  "expr:lt",
  "expr:lte",
  "expr:gt",
  "expr:gte",
  "expr:and",
  "expr:or",
  "expr:not",
  "expr:add",
  "expr:sub",
  "expr:mul",
  "expr:div",
  "expr:lit",
  "expr:var:row",
  "expr:var:state",
  "expr:var:input",
  "expr:get",
  "expr:has",
  "expr:coalesce",
  "expr:if",
  "expr:in",
  "expr:exists",
  "expr:count",
  "expr:sum",
  "expr:avg",
  "expr:min",
  "expr:max",
]

/** Current coverage status based on test file analysis */
export function generateCoverageReport (): CoverageReport {
  // This is the source of truth for what Phase 4 conformance covers
  const queryOperators: OperatorCoverage[] = [
    { operator: "source:snap", category: "query", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts", "sqlite-random-vs-oracle.test.ts"], notes: "Primary source type" },
    { operator: "source:join", category: "query", status: "covered", testFiles: ["sqlite-exec-vs-oracle-smoke.test.ts", "sqlite-exec-vs-oracle.test.ts"], notes: "Single-key equi-join covered; complex multi-joins deferred" },
    { operator: "op:filter", category: "query", status: "covered", testFiles: ["sqlite-random-vs-oracle.test.ts", "sqlite-exec-vs-oracle.test.ts"], notes: "WHERE clause equivalence" },
    { operator: "op:project", category: "query", status: "covered", testFiles: ["sqlite-random-vs-oracle.test.ts", "sqlite-exec-vs-oracle.test.ts"], notes: "SELECT field mapping" },
    { operator: "op:order_by", category: "query", status: "covered", testFiles: ["sqlite-random-vs-oracle.test.ts"], notes: "ORDER BY with direction" },
    { operator: "op:limit", category: "query", status: "covered", testFiles: ["sqlite-random-vs-oracle.test.ts"], notes: "LIMIT clause" },
    { operator: "op:offset", category: "query", status: "covered", testFiles: ["sqlite-random-vs-oracle.test.ts"], notes: "OFFSET clause" },
    { operator: "op:group_by", category: "query", status: "partial", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Basic grouping; complex aggregates deferred" },
    { operator: "op:having", category: "query", status: "deferred", testFiles: [], notes: "Not represented in current QueryV0 AST; deferred until operator is introduced" },
    { operator: "op:distinct", category: "query", status: "uncovered", testFiles: [], notes: "SELECT DISTINCT not yet in conformance suite" },
    { operator: "op:setOp", category: "query", status: "uncovered", testFiles: [], notes: "UNION/INTERSECT/EXCEPT not yet in conformance suite" },
  ]

  const exprOperators: OperatorCoverage[] = [
    { operator: "expr:eq", category: "expr", status: "covered", testFiles: ["sqlite-random-vs-oracle.test.ts", "sqlite-exec-vs-oracle.test.ts"], notes: "Equality comparison" },
    { operator: "expr:neq", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Not-equal comparison" },
    { operator: "expr:lt", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Less-than comparison" },
    { operator: "expr:lte", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Less-than-or-equal comparison" },
    { operator: "expr:gt", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Greater-than comparison" },
    { operator: "expr:gte", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Greater-than-or-equal comparison" },
    { operator: "expr:and", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Boolean AND" },
    { operator: "expr:or", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Boolean OR" },
    { operator: "expr:not", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Boolean NOT" },
    { operator: "expr:add", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Arithmetic addition" },
    { operator: "expr:sub", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Arithmetic subtraction" },
    { operator: "expr:mul", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Arithmetic multiplication" },
    { operator: "expr:div", category: "expr", status: "partial", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Division; NULL handling edge cases deferred" },
    { operator: "expr:lit", category: "expr", status: "covered", testFiles: ["sqlite-random-vs-oracle.test.ts", "sqlite-exec-vs-oracle.test.ts"], notes: "Literal values" },
    { operator: "expr:var:row", category: "expr", status: "covered", testFiles: ["sqlite-random-vs-oracle.test.ts", "sqlite-exec-vs-oracle.test.ts"], notes: "Row field access" },
    { operator: "expr:var:state", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "State variable access" },
    { operator: "expr:var:input", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Input variable access" },
    { operator: "expr:get", category: "expr", status: "partial", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Object field access; nested paths deferred" },
    { operator: "expr:has", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Object field existence check" },
    { operator: "expr:coalesce", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "COALESCE NULL handling" },
    { operator: "expr:if", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "Conditional expression" },
    { operator: "expr:in", category: "expr", status: "partial", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "IN list/subquery; subquery variant deferred" },
    { operator: "expr:exists", category: "expr", status: "deferred", testFiles: [], notes: "EXISTS subquery - deferred to Phase 4+" },
    { operator: "expr:count", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "COUNT aggregation" },
    { operator: "expr:sum", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "SUM aggregation" },
    { operator: "expr:avg", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "AVG aggregation" },
    { operator: "expr:min", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "MIN aggregation" },
    { operator: "expr:max", category: "expr", status: "covered", testFiles: ["sqlite-exec-vs-oracle.test.ts"], notes: "MAX aggregation" },
  ]

  const allOperators = [...queryOperators, ...exprOperators]
  const covered = allOperators.filter(o => o.status === "covered").length
  const partial = allOperators.filter(o => o.status === "partial").length
  const uncovered = allOperators.filter(o => o.status === "uncovered").length
  const deferred = allOperators.filter(o => o.status === "deferred").length
  const totalOperators = allOperators.length

  // Calculate coverage percent (covered = 1, partial = 0.5)
  const coveragePercent = Math.round(((covered + partial * 0.5) / totalOperators) * 100)

  // Identify gaps
  const gaps = allOperators
    .filter(o => o.status === "uncovered" || o.status === "deferred")
    .map(o => ({
      operator: o.operator,
      priority: o.operator.includes("join") || o.operator.includes("group") ? "high" as const : "medium" as const,
      reason: o.notes || "Not yet implemented",
    }))

  return {
    generatedAt: new Date().toISOString(),
    summary: {
      totalOperators,
      covered,
      partial,
      uncovered,
      deferred,
      coveragePercent,
    },
    queryOperators,
    exprOperators,
    gaps,
  }
}

/** Generate and optionally write coverage report */
export function writeCoverageReport (outputPath?: string): CoverageReport {
  const report = generateCoverageReport()
  
  const output = `# CICSC Conformance Operator Coverage Report
Generated: ${report.generatedAt}

## Summary
| Metric | Count |
|--------|-------|
| Total Operators | ${report.summary.totalOperators} |
| Covered | ${report.summary.covered} |
| Partial | ${report.summary.partial} |
| Uncovered | ${report.summary.uncovered} |
| Deferred | ${report.summary.deferred} |
| **Coverage** | **${report.summary.coveragePercent}%** |

## Query Operators
| Operator | Status | Test Files | Notes |
|----------|--------|------------|-------|
${report.queryOperators.map(o => `| ${o.operator} | ${o.status} | ${o.testFiles.join(", ") || "-"} | ${o.notes || ""} |`).join("\n")}

## Expression Operators
| Operator | Status | Test Files | Notes |
|----------|--------|------------|-------|
${report.exprOperators.map(o => `| ${o.operator} | ${o.status} | ${o.testFiles.join(", ") || "-"} | ${o.notes || ""} |`).join("\n")}

## Coverage Gaps
| Operator | Priority | Reason |
|----------|----------|--------|
${report.gaps.map(g => `| ${g.operator} | ${g.priority} | ${g.reason} |`).join("\n")}

## Phase 4 Acceptance Criteria (P4.2.5)
- [x] Coverage report shows gap areas explicitly
- [ ] CI fails on any regression in required conformance suites
- [ ] Coverage report is generated as CI artifact
`

  if (outputPath) {
    fs.writeFileSync(outputPath, output, "utf-8")
  }

  return report
}

function isDirectCliInvocation (): boolean {
  const argv1 = process.argv[1]
  if (!argv1) return false
  return path.resolve(argv1) === fileURLToPath(import.meta.url)
}

// CLI usage
if (isDirectCliInvocation()) {
  const outputPath = process.argv[2]
  const report = writeCoverageReport(outputPath)
  
  if (!outputPath) {
    console.log(`\nConformance Coverage: ${report.summary.coveragePercent}%`)
    console.log(`  Covered: ${report.summary.covered}`)
    console.log(`  Partial: ${report.summary.partial}`)
    console.log(`  Uncovered: ${report.summary.uncovered}`)
    console.log(`  Deferred: ${report.summary.deferred}`)
    console.log(`\nGaps (${report.gaps.length}):`)
    for (const gap of report.gaps) {
      console.log(`  [${gap.priority}] ${gap.operator}: ${gap.reason}`)
    }
  } else {
    console.log(`Coverage report written to: ${outputPath}`)
  }
}
