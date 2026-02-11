# CICSC v0 — Normative Specification

## 0. Status

This document defines CICSC v0.

This specification is normative.
All conforming implementations MUST implement this specification.

---

## 1. Scope

CICSC defines a compiler architecture for constructing socio-technical control systems whose evolution is invariant under replay-verified, total migrations.

---

## 2. Core Concepts

### 2.1 System

A system S is defined by:

- Spec version  
- Core IR  
- event history  
- snapshots  
- projections  
- SLA status  

### 2.2 State

A state s ∈ S is reducible from history under Core IR.

---

## 3. Evolution

### 3.1 Transformation

A transformation τ is defined as:

```
τ := cutover ∘ compile ∘ migrate
```

where:

- migrate: historyₙ → historyₙ₊₁ (total)
- compile: Specₙ₊₁ → Core IRₙ₊₁
- cutover: switch active version pointer

---

### 3.2 Admissibility

τ is admissible iff:

- migrate is total  
- replay verification succeeds  
- functional invariants hold  
- transformability is preserved  

---

## 4. Guarantees

CICSC guarantees:

- history preservation  
- functional preservation  
- transformability preservation  

Only if all admissibility conditions are satisfied.

---

## 5. Semantic Closure

All semantics affecting runtime behavior MUST be expressed in Spec and compiled to Core IR.

Out-of-band semantics are forbidden.

---

## 6. Compilation

Spec DSL MUST compile to Core IR.

Core IR MUST compile to a Target Adapter.

---

## 7. Runtime Model

Runtime execution MUST:

- append events  
- apply reducers  
- enforce guards and constraints  
- maintain projections  
- enforce SLAs  

All execution MUST be derivable from Core IR.

---

## 8. Migration Protocol

Migration MUST:

- create new versioned storage  
- transform all historical events  
- rebuild snapshots and projections  
- replay verify all constraints and SLAs  

---

## 9. Conformance

An implementation conforms to CICSC v0 iff:

- it implements Core IR v0  
- it enforces semantic closure  
- it rejects partial migrations  
- it enforces replay verification  
- it rejects unsupported semantics  

---

## 10. Undefined Behavior

Any behavior outside this specification is undefined.

Undefined behavior invalidates CICSC conformance.
