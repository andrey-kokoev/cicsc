# AGENTS_MAIN.md

Main agent orchestration guide. See [AGENTS.md](AGENTS.md) for overview.

---

## Role

Add work to ledger and maintain governance merge boundary.
Mechanistic core handles assignment and worker closure.

---

## Quick Reference

<!-- generated:main_quick_reference:start -->
```bash
# Validate state
./control-plane/validate.sh

# Add new phase (phase ID auto-generated)
./control-plane/add_phase.sh --number 62 --title "New Feature"

# Add checkboxes to existing milestone
./control-plane/add_checkbox.sh --milestone CF1 --checkbox "CF1.1:description"

# Merge completed work (governance boundary)
git fetch origin
git merge --ff-only origin/feat/branch-name

# Push to main
git push origin main
```
<!-- generated:main_quick_reference:end -->

---

## Workflow

### 1. Assess State

```bash
./control-plane/validate.sh
```

### 2. Add Work

```bash
./control-plane/add_phase.sh --number 62 --title "New Feature"
./control-plane/add_checkbox.sh --milestone CF1 --checkbox "CF1.1:description"
```

That's it. Mechanistic core (`autoassign.sh`) assigns to `standing_by` agents with fresh heartbeats.

If you create a new phase without `--checkboxes`, create a milestone before
adding checkboxes to it.

### 3. Merge

When worker pushes branch:
```bash
git fetch origin
git merge --ff-only origin/feat/branch-name
./control-plane/validate.sh
git push origin main
```

`integrate.sh` is executed by worker daemon closure flow (`worker-run-assignment.sh`).
Main remains merge/governance authority for `main`.

---

## Principles

- **Just add work** - Don't dispatch, autoassign handles it
- **Validate after every merge** - Never skip gates
- **Use scripts** - Never edit state directly
- **Do not close assignments manually** - Worker daemon owns assignment closure

---

## Common Tasks

| Task | Command |
|------|---------|
| Check state | `./control-plane/validate.sh` |
| Add phase | `./control-plane/add_phase.sh` |
| Add checkbox | `./control-plane/add_checkbox.sh` |
| Merge | `git merge --ff-only origin/feat/...` |
