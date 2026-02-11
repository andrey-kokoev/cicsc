# /docs/spec/security.md

# Security Model (Normative)

## 0. Status

This document defines the security model for CICSC v0.

This specification is normative.

---

## 1. Trust Model

CICSC assumes:

- Spec authors are trusted to define correct semantics  
- runtime operators are untrusted with respect to semantic closure  
- adapters are part of the trusted computing base  

---

## 2. Attack Surface

The primary attack surfaces are:

- Spec DSL input  
- Core IR bundles  
- adapter lowering  
- runtime execution of queries and reducers  
- migration transforms  

---

## 3. Input Validation

Implementations MUST:

- validate Spec DSL before compilation  
- validate Core IR against schema  
- validate migrations for totality  
- validate adapter capability compatibility  

Invalid input MUST be rejected.

---

## 4. Execution Safety

Implementations MUST:

- sandbox Core IR expression evaluation  
- prevent arbitrary code execution  
- enforce resource limits on queries  
- prevent injection via payload or expressions  

---

## 5. Authorization

Authorization MUST be:

- expressed in Spec  
- compiled into Core IR  
- enforced at runtime  

Out-of-band authorization is forbidden.

---

## 6. Isolation

Multi-tenant implementations MUST isolate:

- event logs  
- snapshots  
- projections  
- SLA status  

Cross-tenant access is forbidden.

---

## 7. Audit Logging

Implementations MUST log:

- compilation artifacts  
- migrations  
- replay verification results  
- runtime errors  

Logs MUST be tamper-evident.

---

## 8. Secrets

Adapters MUST NOT store secrets in Core IR or Spec DSL.

Secrets MUST be injected at runtime via secure configuration mechanisms.

---

## 9. Denial of Service

Implementations SHOULD enforce:

- rate limits on commands  
- limits on history replay  
- bounds on query complexity  

---

## 10. Conformance

Violations of this security model invalidate CICSC conformance.
