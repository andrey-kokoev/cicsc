# Limits and Non-Goals (Normative)

## 0. Status

This document defines explicit limits and non-goals of CICSC v0.

This specification is normative.

---

## 1. Closed World Assumption

CICSC v0 assumes a closed semantic world:

- all semantics must be Spec-expressible  
- external systems must be modeled explicitly  
- implicit side effects are forbidden  

Open-world reasoning is out of scope.

---

## 2. Expressiveness Limits

CICSC v0 does not support:

- arbitrary graph traversals in constraints  
- recursive queries  
- unbounded joins  
- user-defined functions in Core IR  
- non-total reducers  
- partial migrations  

Any such construct MUST be rejected.

---

## 3. Performance Non-Goals

CICSC v0 does not optimize for:

- extreme throughput  
- low-latency distributed transactions  
- real-time streaming analytics  

Correctness and invariance take precedence.

---

## 4. Concurrency Model

CICSC v0 does not define:

- distributed consensus  
- cross-entity transactional semantics beyond single-entity + constraint checks  

Adapters MAY provide stronger guarantees, but semantics MUST remain within Core IR.

---

## 5. UI and UX

CICSC v0 does not define:

- user interfaces  
- dashboards  
- visualization layers  

These are outside the substrate.

---

## 6. Extensibility

All extensions require:

- Core IR version bump  
- Spec DSL update  
- adapter interface update  
- migration compatibility strategy  

Silent extension is forbidden.

---

## 7. Conformance

Violation of these limits invalidates CICSC conformance.
