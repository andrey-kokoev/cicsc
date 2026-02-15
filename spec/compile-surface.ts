import { parseDSL } from "./parse-dsl"
import { compileSpecV0ToCoreIr } from "./compile-to-ir"
import type { CoreIrV0 } from "../core/ir/types"

export function compileSurfaceToIr(input: string): CoreIrV0 {
  const spec = parseDSL(input);
  return compileSpecV0ToCoreIr(spec);
}
