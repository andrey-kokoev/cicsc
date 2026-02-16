# AGENTS_WORKER.md

Worker agent implementation guide. See [AGENTS.md](AGENTS.md) for overview.

---

## Role

Implement assigned work, follow workflow, push feature branches.

---

## Quick Reference

```bash
# Onboard
./control-plane/onboard.sh AGENT_KIMI

# Sync with main
git fetch origin && git rebase origin/main

# Check inbox
./control-plane/inbox.sh AGENT_KIMI

# Claim work
./control-plane/claim.sh AGENT_KIMI

# Implement (in worktree)

# Run gates
./control-plane/check_gates.sh

# Complete work
./control-plane/complete.sh BZ1.1

# Push branch
git push origin feat/description
```

---

## Workflow

### 1. Start

Onboard:
```bash
./control-plane/onboard.sh AGENT_KIMI
```

Sync:
```bash
git fetch origin && git rebase origin/main
```

### 2. Check Assignments

```bash
./control-plane/inbox.sh AGENT_KIMI
```

### 3. Claim Work

```bash
./control-plane/claim.sh AGENT_KIMI
```

This marks assignments as `in_progress`.

### 4. Implement

Create feature branch if needed:
```bash
git checkout -b feat/description origin/main
```

Make changes, commit:
```bash
git add -A && git commit -m "feat: description"
```

### 5. Run Gates

Before completing:
```bash
./control-plane/check_gates.sh
```

### 6. Complete

```bash
./control-plane/complete.sh BZ1.1
```

This:
- Updates assignments.yaml to `done`
- Updates execution-ledger.yaml
- Runs gates automatically

### 7. Push

```bash
git push origin feat/description
```

### 8. Notify Main

Done. Main agent will merge.

---

## Worktree Usage

Worktrees auto-sync when you run:
- `inbox.sh`
- `claim.sh`
- `complete.sh`
- `check_gates.sh`

Use `--no-sync` to skip if needed:
```bash
./control-plane/inbox.sh AGENT_KIMI --no-sync
```

---

## Important Rules

1. **Never edit YAML directly** - Use scripts
2. **Never commit to main** - Always feature branch
3. **Always run gates** - Before completing
4. **Always complete work** - Don't skip
5. **Sync before starting** - Rebase origin/main

---

## Common Tasks

| Task | Command |
|------|---------|
| Sync | `git fetch origin && git rebase origin/main` |
| Inbox | `./control-plane/inbox.sh AGENT_KIMI` |
| Claim | `./control-plane/claim.sh AGENT_KIMI` |
| Gates | `./control-plane/check_gates.sh` |
| Complete | `./control-plane/complete.sh BZ1.1` |
| Push | `git push origin feat/branch-name` |

---

## Tips

- Worktrees are isolated - safe to experiment
- Gates catch most issues early
- If rebase fails, resolve conflicts and continue
- Main will merge via FF-only
