# Bundle Compatibility Matrix

CICSC uses a SemVer-based compatibility model for bundles and tenants.

## Compatibility Rules

- **Major Version:** Breaking changes. A tenant using `1.x.y` cannot automatically upgrade to `2.x.y`.
- **Minor Version:** Feature additions (non-breaking). Upgrading from `1.1.x` to `1.2.x` is always allowed.
- **Patch Version:** Bug fixes (non-breaking).

## Compatibility Checker

The system uses `core/ir/semver.ts` to verify if a requested bundle version is compatible with the installed version.

```typescript
export function isCompatible(requested: string, available: string): boolean {
  const r = parseSemVer(requested);
  const a = parseSemVer(available);

  // Simple compatibility rule: same major version
  return r.major === a.major && compareSemVer(available, requested) >= 0;
}
```

## Dependency Resolution

When a bundle depends on another bundle, the version range is checked against the registered versions in the KV index.
Currently, only exact major version matching is enforced automatically.
