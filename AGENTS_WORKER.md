# AGENTS_WORKER.md

Worker agent implementation guide. See [AGENTS.md](AGENTS.md) for overview.

---

## Role

Implement assigned work, follow workflow, push feature branches.

---

## Quick Reference

<!-- generated:worker_quick_reference:start -->
```bash
# Set your agent ID (do once)
export AGENT_ID=AGENT_GEMINI

# Start standby - polls for assigned work
./control-plane/standby.sh

# Work automatically assigned when core assigns to you
```
<!-- generated:worker_quick_reference:end -->

---

## Workflow

### 1. Sync

```bash
git fetch origin && git rebase origin/main
```

### 2. Standby

```bash
export AGENT_ID=AGENT_GEMINI
./control-plane/standby.sh
```

This polls every 5 seconds. When work is assigned to you, it outputs:
```
WORK ASSIGNED: CF1.1
Task: description here
```

### 3. Work

Implement in your worktree.

### 4. Gates

```bash
./control-plane/check_gates.sh
```

### 5. Push

```bash
git push origin feat/description
```

After push, Main performs FF integration and closes the checkbox.
Commit/push alone does not close the assignment.

---

## Worktree Usage

Keep your worktree in sync manually:

```bash
git fetch origin && git rebase origin/main
```

---

## Important Rules

1. **Never edit state directly** - Use scripts
2. **Never commit to main** - Always feature branch
3. **Always run gates** - Before pushing
4. **Push, then Main integrates** - Completion happens at integration boundary
5. **Sync before starting** - Rebase origin/main

---

## Common Tasks

| Task | Command |
|------|---------|
| Sync | `git fetch origin && git rebase origin/main` |
| Standby | `export AGENT_ID=AGENT_GEMINI && ./control-plane/standby.sh` |
| Gates | `./control-plane/check_gates.sh` |
| Push | `git push origin feat/branch-name` |

---

## Tips

- Worktrees are isolated - safe to experiment
- Gates catch most issues early
- If rebase fails, resolve conflicts and continue
- Main will merge via FF-only
