import type { BundleV1 } from "../../core/ir/bundle";
import { isCompatible } from "../../core/ir/semver";
import { KVBundleIndex } from "./kv-bundle-index";

export class DependencyResolver {
  constructor(private kvIndex: KVBundleIndex) {}

  async resolveDependencies(bundle: BundleV1): Promise<Record<string, string>> {
    const resolved: Record<string, string> = {};
    const deps = bundle.manifest.dependencies || {};

    for (const [name, versionRange] of Object.entries(deps)) {
      // Find latest compatible version
      const latestDigest = await this.kvIndex.getDigest(name, "latest");
      if (!latestDigest) {
        throw new Error(`Dependency ${name} not found in registry`);
      }
      
      // Real impl would fetch bundle manifest and check version range
      // For now, assume latest is OK if compatible major version
      resolved[name] = latestDigest;
    }

    return resolved;
  }
}
