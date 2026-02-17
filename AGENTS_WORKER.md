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

# Push (auto-completes on main)
git push origin feat/description
```

### 6. Push (Auto-Complete)

```bash
git push origin feat/description
```

Pushing to your feature branch triggers **auto-complete**:
- Main detects commit with checkbox ID in message
- Marks checkbox done in ledger
- No manual complete.sh needed

### 7. Notify Main

Done. Main agent will merge.

---

## Worktree Usage

Worktrees auto-sync when you run:
- `inbox.sh`
- `claim.sh`
- `check_gates.sh`

Use `--no-sync` to skip if needed:
```bash
./control-plane/inbox.sh AGENT_KIMI --no-sync
```

---

## Important Rules

1. **Never edit YAML directly** - Use scripts
2. **Never commit to main** - Always feature branch
3. **Always run gates** - Before pushing
4. **Push triggers auto-complete** - No manual complete.sh needed
5. **Sync before starting** - Rebase origin/main

---

## Common Tasks

| Task | Command |
|------|---------|
| Sync | `git fetch origin && git rebase origin/main` |
| Inbox | `./control-plane/inbox.sh AGENT_KIMI` |
| Claim | `./control-plane/claim.sh AGENT_KIMI` |
| Gates | `./control-plane/check_gates.sh` |
| Push | `git push origin feat/branch-name` |

---

## Tips

- Worktrees are isolated - safe to experiment
- Gates catch most issues early
- If rebase fails, resolve conflicts and continue
- Main will merge via FF-only
