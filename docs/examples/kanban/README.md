# /docs/examples/kanban/README.md

# Kanban — Reference Vertical (CICSC v0)

## 0. Status

This directory contains a complete reference implementation of a Kanban-style flow control system specified in CICSC Spec DSL and compiled to Core IR v0.

This example is normative for demonstrating CICSC applicability to flow systems.

---

## 1. Scope

This example demonstrates:

- flow states and transitions
- WIP constraints (global invariants)
- queue views (lanes)
- metrics views
- migrations

---

## 2. Files

```
/docs/examples/kanban/
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

## 5. WIP Constraint Example

The Kanban WIP limit is enforced as a `bool_query` constraint over snapshots:

- group_by: state
- count: items per lane
- assert: count < limit

Compilation MUST fail if the backend cannot represent this constraint.

---

## 6. Conformance

This example MUST:

- enforce WIP limits  
- preserve history under migrations  
- reject non-total upgrades  

Any deviation invalidates CICSC conformance.
