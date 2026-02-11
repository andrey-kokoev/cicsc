# CICSC CLI — Reference Interface (Informative)

## 0. Status

This document describes the reference command-line interface for CICSC.

This document is informative and does not define normative semantics.

---

## 1. Commands

### 1.1 Compile

```bash
cicsc compile <spec.cicsc> --target <adapter> --out <bundle_dir>
```

Compiles Spec DSL to Core IR and lowers to a runtime bundle for the specified adapter.

Errors MUST be reported if:

- Spec is invalid  
- Core IR cannot be generated  
- adapter capabilities are insufficient  

---

### 1.2 Run

```bash
cicsc run --bundle <bundle_dir> --db <db_path>
```

Starts the runtime for the compiled bundle.

---

### 1.3 Migrate

```bash
cicsc migrate --from <version> --to <version> --bundle <bundle_dir> --db <db_path> --verify
```

Materializes and verifies migrations.

Cutover MUST NOT occur unless `--verify` succeeds.

---

### 1.4 Validate

```bash
cicsc validate <spec.cicsc>
```

Validates Spec DSL and Core IR compilation without producing a bundle.

---

### 1.5 Inspect

```bash
cicsc inspect <bundle_dir>
```

Prints bundle metadata: versions, hashes, capabilities.

---

## 2. Exit Codes

- `0` success  
- `1` Spec validation error  
- `2` Core IR validation error  
- `3` adapter capability mismatch  
- `4` migration verification failure  
- `5` runtime error  

---

## 3. Determinism

CLI output MUST be deterministic given identical inputs.

---

## 4. Logging

CLI MUST log:

- compilation hash  
- Core IR hash  
- adapter version  
- timestamp  

---

## 5. Non-Goals

The CLI is not a management UI.

Interactive administration is out of scope.
