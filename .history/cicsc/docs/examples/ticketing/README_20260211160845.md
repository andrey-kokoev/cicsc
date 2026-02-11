# /docs/examples/ticketing/README.md

# Ticketing — Reference Vertical (CICSC v0)

## 0. Status

This directory contains a complete reference implementation of a ticketing system specified in CICSC Spec DSL and compiled to Core IR v0.

This example is normative for demonstrating end-to-end CICSC usage.

---

## 1. Scope

This example demonstrates:

- entity definition
- commands and reducers
- constraints
- SLAs
- views
- migrations
- compilation to SQLite/D1

---

## 2. Files

```
/docs/examples/ticketing/
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

## 5. Invariance Checks

Before cutover:

```bash
cicsc migrate --verify --from v0 --to v1 --db ./db.sqlite
```

Cutover MUST NOT occur unless replay verification succeeds.

---

## 6. Conformance

Any modification to this example MUST preserve CICSC v0 conformance.

Non-conforming examples MUST NOT be used as references.
