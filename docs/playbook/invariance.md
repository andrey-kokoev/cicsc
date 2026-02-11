# /docs/playbook/invariance.md

# Constructive Invariance — Operational Playbook

## 0. Status

This document describes the operational discipline required to preserve constructive invariance when using CICSC.

This document is informative but binding for conformance in practice.

---

## 1. Invariance Discipline

All system evolution MUST occur via:

- Spec changes
- compiled Core IR changes
- executable migrations
- replay-verified cutovers

No other form of system evolution is permitted.

---

## 2. Allowed Evolution

Allowed changes:

- adding new commands
- adding new events
- adding new states
- adding new constraints
- adding new views
- adding new SLAs
- adding new entities
- adding new projections
- adding new shadow fields

All allowed changes MUST:

- compile to Core IR  
- be accompanied by total migrations  
- pass replay verification  

---

## 3. Disallowed Evolution

Disallowed changes:

- deleting historical events  
- mutating historical events  
- changing event semantics without migration  
- bypassing Core IR  
- manual database edits  
- partial migrations  
- best-effort data fixes  

Any of these invalidate constructive invariance.

---

## 4. Versioning

Each Spec version MUST:

- have an explicit version number  
- define migrations from previous versions  
- define compatibility constraints  

Multiple active versions MUST NOT exist per tenant.

---

## 5. Replay Verification Procedure

Before cutover:

1. materialize new versioned storage  
2. apply migration to historical events  
3. rebuild snapshots and projections  
4. replay all constraints and SLAs  
5. verify no violations  

Cutover MUST NOT occur unless all checks pass.

---

## 6. Rollback

Rollback MUST be performed by:

- switching active version pointer  
- preserving all historical versions  

Rollback MUST NOT mutate history.

---

## 7. Auditability

All versions, migrations, and replay results MUST be auditable.

Audit logs MUST include:

- Spec version  
- migration hash  
- replay result summary  
- timestamp  

---

## 8. Failure Handling

On failure:

- system MUST remain on previous version  
- new version storage MUST be discarded or isolated  
- no partial cutover is permitted  

---

## 9. Operational Guarantees

Following this playbook guarantees:

- history preservation  
- functional preservation  
- transformability preservation  

Violation of this playbook invalidates CICSC conformance.
