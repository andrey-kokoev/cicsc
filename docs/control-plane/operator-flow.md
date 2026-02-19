# Operator Flow

Canonical source for AGENTS operator snippets.

## Snippets

### `main_quick_reference`

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

### `worker_quick_reference`

```bash
# Set your agent ID (do once)
export AGENT_ID=AGENT_GEMINI

# Start daemon (blocking loop)
./control-plane/agentd.sh run --agent "$AGENT_ID"

# Check authoritative status
./control-plane/status.sh --agent "$AGENT_ID" --json
./control-plane/status.sh --summary --json

# Stop daemon gracefully
./control-plane/agentd.sh stop --agent "$AGENT_ID"
```
