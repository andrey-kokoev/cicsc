# AGENTS_MAIN.md

Main agent orchestration guide. See [AGENTS.md](AGENTS.md) for overview.

---

## Role

Add work to ledger, maintain state. Mechanistic core handles assignment.

---

## Quick Reference

```bash
# Validate state
./control-plane/validate.sh

# Add new phase
./control-plane/add_phase.sh --id CF --number 62 --title "New Feature"

# Add checkboxes to existing milestone
./control-plane/add_checkbox.sh --milestone CF1 --checkbox "CF1.1:description"

# Merge completed work
git fetch origin
git merge --ff-only origin/feat/branch-name
./control-plane/integrate.sh integrate CF1.1

# Push to main
git push origin main
```

---

## Workflow

### 1. Assess State

```bash
./control-plane/validate.sh
```

### 2. Add Work

```bash
./control-plane/add_phase.sh --id CF --number 62 --title "New Feature"
./control-plane/add_checkbox.sh --milestone CF1 --checkbox "CF1.1:description"
```

That's it. Mechanistic core (`autoassign.sh`) assigns to idle agents automatically.

### 3. Integrate

When worker pushes branch:
```bash
git fetch origin
git merge --ff-only origin/feat/branch-name
./control-plane/integrate.sh integrate CF1.1
./control-plane/validate.sh
git push origin main
```

---

## Principles

- **Just add work** - Don't dispatch, autoassign handles it
- **Validate after every merge** - Never skip gates
- **Use scripts** - Never edit state directly

---

## Common Tasks

| Task | Command |
|------|---------|
| Check state | `./control-plane/validate.sh` |
| Add phase | `./control-plane/add_phase.sh` |
| Add checkbox | `./control-plane/add_checkbox.sh` |
| Merge | `git merge --ff-only origin/feat/...` |
