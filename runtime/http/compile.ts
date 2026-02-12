// /runtime/http/compile.ts

import type { CoreIrBundleV0, CoreIrV0 } from "../../core/ir/types"
import { parseSpecV0 } from "../../spec/parse-yaml"
import { compileSpecV0ToCoreIr } from "../../spec/compile-to-ir"
import { typecheckSpecV0 } from "../../spec/typecheck"
import { typecheckCoreIrV0 } from "../../core/ir/typecheck"

/**
 * Compile Spec (YAML string or JSON object) -> validated CoreIrBundleV0
 *
 * v0 contract:
 * - Spec DSL shape uses `entities` (not IR `types`) and compiles to Core IR.
 * - Expressions/queries remain tagged-object form in v0.
 * - This function compiles + typechecks; schema generation happens at install time.
 */
export function compileSpecToBundleV0 (input: string | unknown): CoreIrBundleV0 {
  const spec = parseSpecV0(input)
  const stc = typecheckSpecV0(spec)
  if (!stc.ok) {
    const first = stc.errors[0]!
    throw new Error(`spec typecheck failed at ${first.path}: ${first.message}`)
  }

  const ir = compileSpecV0ToCoreIr(spec)

  const tc = typecheckCoreIrV0(ir)
  if (!tc.ok) {
    const first = tc.errors[0]!
    throw new Error(`typecheck failed at ${first.path}: ${first.message}`)
  }

  return { core_ir: ir } as CoreIrBundleV0
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
