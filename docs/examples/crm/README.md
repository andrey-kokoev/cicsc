# /docs/examples/crm/README.md

# CRM — Reference Vertical (CICSC v0)

## 0. Status

This directory contains a complete reference implementation of a CRM-style pipeline system specified in CICSC Spec DSL and compiled to Core IR v0.

This example is normative for demonstrating CICSC applicability to pipeline and revenue-tracking systems.

---

## 1. Scope

This example demonstrates:

- pipeline stages and transitions  
- lead and opportunity entities  
- ownership and authorization  
- conversion metrics  
- SLAs on follow-up  
- migrations  

---

## 2. Files

```
/docs/examples/crm/
  spec.cicsc           # Spec DSL source
  ir.json              # compiled Core IR
  bundle/              # generated runtime bundle
  README.md            # this file
```

---

## 3. Build Procedure

```bash
cicsc compile spec.cicsc --target sqlite --out bundle
```

---

## 4. Run Procedure

```bash
cd bundle
cicsc run --db ./db.sqlite
```

---

## 5. Pipeline Metrics

This example includes:

- stage counts  
- conversion rates  
- aging metrics  

All metrics MUST be representable as Core IR views or bool_query constraints.

---

## 6. Conformance

This example MUST preserve:

- invariant-preserving evolution  
- replay-verifiable migrations  
- semantic closure  

Any deviation invalidates CICSC conformance.
