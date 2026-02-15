import { createHash } from "node:crypto";
import type { BundleV1 } from "./bundle";

export type BundleValidationError = {
  path: string;
  message: string;
};

export function validateBundleV1Integrity(bundle: any): { ok: true; value: BundleV1 } | { ok: false; errors: BundleValidationError[] } {
  const errors: BundleValidationError[] = [];

  if (bundle.kind !== "cicsc/bundle") errors.push({ path: "kind", message: "must be cicsc/bundle" });
  if (bundle.version !== 1) errors.push({ path: "version", message: "must be 1" });
  if (!bundle.manifest) errors.push({ path: "manifest", message: "is required" });
  if (!bundle.core_ir) errors.push({ path: "core_ir", message: "is required" });
  
  if (errors.length > 0) return { ok: false, errors };

  if (bundle.digest) {
    const { digest, ...rest } = bundle;
    const hash = createHash("sha256");
    hash.update(JSON.stringify(rest));
    const calculated = hash.digest("hex");
    if (calculated !== digest) {
      errors.push({ path: "digest", message: `mismatch: expected ${digest}, got ${calculated}` });
      return { ok: false, errors };
    }
  } else {
     errors.push({ path: "digest", message: "digest is required for integrity verification" });
     return { ok: false, errors };
  }

  return { ok: true, value: bundle as BundleV1 };
}
