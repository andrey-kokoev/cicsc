import type { VmIntrinsics } from "./eval"

export type AuthIntrinsicContractError = {
  path: string
  message: string
}

export function validateAuthIntrinsicsContract (intrinsics: Partial<VmIntrinsics>): {
  ok: true
} | {
  ok: false
  errors: AuthIntrinsicContractError[]
} {
  const errors: AuthIntrinsicContractError[] = []

  if (typeof intrinsics.has_role !== "function") {
    errors.push({ path: "has_role", message: "has_role(actor, role) => boolean function required" })
  }
  if (typeof intrinsics.role_of !== "function") {
    errors.push({ path: "role_of", message: "role_of(actor) => string function required" })
  }
  if (typeof intrinsics.auth_ok !== "function") {
    errors.push({ path: "auth_ok", message: "auth_ok(actor, cmdref) => boolean function required" })
  }

  if (errors.length) return { ok: false, errors }
  return { ok: true }
}
