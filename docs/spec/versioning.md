# /docs/spec/versioning.md

# Versioning and Compatibility (Normative)

## 0. Status

This document defines versioning and compatibility rules for CICSC v0.

This specification is normative.

---

## 1. Spec Versioning

Each Spec MUST declare a monotonically increasing version number.

Spec versions MUST be integers starting at 0.

Multiple active Spec versions per tenant are forbidden.

---

## 2. Core IR Versioning

Each Core IR bundle MUST declare:

```json
{ "core_ir_version": 0 }
```

Adapters MUST reject bundles with unsupported Core IR versions.

---

## 3. Adapter Versioning

Adapters MUST declare:

- supported Core IR versions  
- supported Spec DSL versions  

Compilation MUST fail if version compatibility is violated.

---

## 4. Migration Compatibility

For any Spec version N → N+1:

- a migration MUST exist  
- the migration MUST be total  
- replay verification MUST succeed  

Skipping versions is forbidden.

---

## 5. Backward Compatibility

Backward compatibility is not guaranteed prior to CICSC v1.0.

Spec authors MUST provide migrations for all changes.

---

## 6. Forward Compatibility

Implementations MAY reject unknown future versions.

Silent fallback behavior is forbidden.

---

## 7. Deprecation

Deprecation MUST be explicit:

- deprecated constructs MUST continue to compile until removed in a major version  
- removal MUST increment Core IR version  

---

## 8. Compatibility Matrix

Implementations SHOULD publish a compatibility matrix:

- CICSC Spec version  
- Core IR version  
- Adapter version  

---

## 9. Conformance

Violations of versioning rules invalidate CICSC conformance.
