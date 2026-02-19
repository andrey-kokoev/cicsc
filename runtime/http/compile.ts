// /runtime/http/compile.ts

import type { CoreIrBundleV0, CoreIrV0 } from "../../core/ir/types"
import { parseSpecV0 } from "../../spec/parse-yaml"
import { compileSpecV0ToCoreIr } from "../../spec/compile-to-ir"
import { typecheckSpecV0 } from "../../spec/typecheck"
import { typecheckCoreIrV0 } from "../../core/ir/typecheck"
import { generateUiFromIr } from "../../ui/generator"

export type CompileDiagnostic = {
  layer: "spec" | "ir"
  path: string
  message: string
}

export class CompileDiagnosticsError extends Error {
  diagnostics: CompileDiagnostic[]

  constructor (message: string, diagnostics: CompileDiagnostic[]) {
    super(message)
    this.name = "CompileDiagnosticsError"
    this.diagnostics = diagnostics
  }
}

function unwrapIntentPlaneSpecEnvelope (input: unknown): unknown {
  if (!input || typeof input !== "object" || Array.isArray(input)) {
    return input
  }

  const obj = input as any
  const hasSpec = Object.prototype.hasOwnProperty.call(obj, "spec")
  const hasDeployable = Object.prototype.hasOwnProperty.call(obj, "deployable")
  const hasBlocking = Object.prototype.hasOwnProperty.call(obj, "blocking_issues")
  if (!hasSpec || (!hasDeployable && !hasBlocking)) {
    return input
  }

  const blockingIssues = Array.isArray(obj.blocking_issues)
    ? obj.blocking_issues.filter((x: unknown) => typeof x === "string")
    : []
  const deployable = obj.deployable === true

  if (!deployable || blockingIssues.length > 0) {
    throw new CompileDiagnosticsError(
      "intent-plane preflight failed: unresolved blocking issues",
      blockingIssues.map((issue: string, idx: number) => ({
        layer: "spec",
        path: `$.blocking_issues[${idx}]`,
        message: issue,
      }))
    )
  }

  return obj.spec
}

/**
 * Compile Spec (YAML string or JSON object) -> validated CoreIrBundleV0
 *
 * v0 contract:
 * - Spec DSL shape uses `entities` (not IR `types`) and compiles to Core IR.
 * - Expressions/queries remain tagged-object form in v0.
 * - This function compiles + typechecks; schema generation happens at install time.
 */
export function compileSpecToBundleV0 (input: string | unknown): CoreIrBundleV0 {
  const preflighted = unwrapIntentPlaneSpecEnvelope(input)
  const spec = parseSpecV0(preflighted)
  const stc = typecheckSpecV0(spec)
  if (!stc.ok) {
    const first = stc.errors[0]!
    throw new CompileDiagnosticsError(
      `spec typecheck failed at ${first.path}: ${first.message}`,
      stc.errors.map((e) => ({
        layer: "spec",
        path: e.path,
        message: e.message,
      }))
    )
  }

  const ir = compileSpecV0ToCoreIr(spec)

  const tc = typecheckCoreIrV0(ir)
  if (!tc.ok) {
    const first = tc.errors[0]!
    throw new CompileDiagnosticsError(
      `typecheck failed at ${first.path}: ${first.message}`,
      tc.errors.map((e) => ({
        layer: "ir",
        path: e.path,
        message: e.message,
      }))
    )
  }

  return { core_ir: ir } as CoreIrBundleV0
}

export function compileSpecWithUi(input: string | unknown): { bundle: CoreIrBundleV0; ui: any } {
  const bundle = compileSpecToBundleV0(input)
  const ui = generateUiFromIr(bundle.core_ir)
  return { bundle, ui }
}

/**
 * Helper for HTTP routes: reads request body either as YAML text or JSON.
 *
 * - If content-type contains "yaml" or "text", read as text.
 * - Else try JSON first; if JSON fails, fall back to text.
 */
export async function readSpecBody (req: Request): Promise<string | unknown> {
  const ct = (req.headers.get("content-type") ?? "").toLowerCase()

  if (ct.includes("yaml") || ct.includes("text/plain")) {
    return await req.text()
  }

  // prefer JSON
  try {
    return await req.json()
  } catch {
    return await req.text()
  }
}
