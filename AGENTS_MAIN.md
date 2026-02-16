# AGENTS_MAIN.md

Main agent orchestration guide. See [AGENTS.md](AGENTS.md) for overview.

---

## Role

Orchestrate worker agents, manage dispatch, merge work, maintain execution ledger.

---

## Quick Reference

```bash
# Validate state
./control-plane/validate.sh

# Check phase/milestone status
grep status open control-plane/execution-ledger.yaml

# Add new phase
./control-plane/add_phase.sh --id BZ --number 52 --title "Title" --checkboxes "BZ1.1:desc"

# Add checkboxes to existing milestone
./control-plane/add_checkbox.sh --milestone BZ1 --checkbox "BZ1.1:description"

# Dispatch work to agent
./control-plane/dispatch.sh --checkbox BZ1.1 --agent AGENT_KIMI

# Monitor worker inboxes
./control-plane/inbox.sh AGENT_KIMI

# Merge completed work
git fetch origin
git merge --ff-only origin/feat/branch-name

# Push to main
git push origin main
```

---

## Workflow

### 1. Assess State

```bash
./control-plane/validate.sh
```

Check for open checkboxes:
```bash
grep -A2 "status: open" control-plane/execution-ledger.yaml
```

### 2. Plan Work

Add new phase or checkboxes:
```bash
./control-plane/add_phase.sh --id BZ --number 52 --title "New Feature"
./control-plane/add_checkbox.sh --milestone BZ1 --checkbox "BZ1.1:description"
```

### 3. Dispatch

Assign to worker agent:
```bash
./control-plane/dispatch.sh --checkbox BZ1.1 --agent AGENT_KIMI
git add control-plane/ && git commit -m "dispatch: BZ1.1 -> AGENT_KIMI"
git push origin main
```

### 4. Monitor

Check worker progress:
```bash
./control-plane/inbox.sh AGENT_KIMI
```

### 5. Integrate

When worker completes and pushes branch:
```bash
git fetch origin
git merge --ff-only origin/feat/branch-name
./control-plane/validate.sh
git push origin main
```

---

## Principles

- **Dispatch smallest adjacent steps** - Don't overwhelm workers
- **Validate after every merge** - Never skip gates
- **Use scripts** - Never edit YAML directly
- **Keep ledger clean** - Mark done promptly

---

## Common Tasks

| Task | Command |
|------|---------|
| Check open work | `./control-plane/validate.sh` |
| Add phase | `./control-plane/add_phase.sh` |
| Add checkbox | `./control-plane/add_checkbox.sh` |
| Assign work | `./control-plane/dispatch.sh` |
| Monitor | `./control-plane/inbox.sh` |
| Merge | `git merge --ff-only origin/feat/...` |
