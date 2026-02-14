#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
COLLAB_PATH="${ROOT_DIR}/control-plane/collaboration/collab-model.yaml"

WORKTREE=""
OWNER_AGENT_REF="AGENT_MAIN"
DELEGATED_TO_AGENT_REF=""
ACTION="delegate"
DELEGATION_ID=""
COMMIT_SHA=""
NOTES=""
NO_REFRESH=0
DRY_RUN=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_delegate_worktree.sh \
    --worktree <path> \
    --owner-agent-ref AGENT_... \
    [--delegate-to AGENT_... | --revoke AGENT_...] \
    [options]

Options:
  --worktree <path>         Worktree path to delegate/revoke.
  --owner-agent-ref <id>    Baseline owner agent for the worktree.
  --delegate-to <id>        Delegate effective ownership to this agent.
  --revoke <id>             Revoke active delegation to this agent.
  --delegation-id <id>      Optional delegation id (default auto-generated for delegate).
  --commit <sha>            Commit to bind on delegation entry (default: current HEAD short).
  --notes <text>            Optional notes.
  --no-refresh              Do not regenerate views after update.
  --dry-run                 Validate and print summary, but do not write.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --owner-agent-ref) OWNER_AGENT_REF="${2:-}"; shift 2 ;;
    --delegate-to) DELEGATED_TO_AGENT_REF="${2:-}"; ACTION="delegate"; shift 2 ;;
    --revoke) DELEGATED_TO_AGENT_REF="${2:-}"; ACTION="revoke"; shift 2 ;;
    --delegation-id) DELEGATION_ID="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --notes) NOTES="${2:-}"; shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${WORKTREE}" || -z "${OWNER_AGENT_REF}" || -z "${DELEGATED_TO_AGENT_REF}" ]]; then
  echo "missing required arguments" >&2
  usage >&2
  exit 1
fi

cd "${ROOT_DIR}"
./control-plane/scripts/collab_validate.sh >/dev/null

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

python3 - "$COLLAB_PATH" "$WORKTREE" "$OWNER_AGENT_REF" "$DELEGATED_TO_AGENT_REF" "$ACTION" "$DELEGATION_ID" "$COMMIT_SHA" "$NOTES" "$DRY_RUN" <<'PY'
import re
import sys
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
worktree = sys.argv[2]
owner_agent_ref = sys.argv[3]
delegated_to_agent_ref = sys.argv[4]
action = sys.argv[5]
delegation_id_arg = sys.argv[6]
commit_sha = sys.argv[7]
notes = sys.argv[8]
dry_run = sys.argv[9] == "1"

if action not in {"delegate", "revoke"}:
    raise SystemExit(f"invalid action: {action}")
if not re.fullmatch(r"[0-9a-f]{7,40}", commit_sha):
    raise SystemExit(f"invalid commit sha: {commit_sha}")

data = yaml.safe_load(collab_path.read_text(encoding="utf-8"))
agents = {a.get("id") for a in data.get("agents", [])}
worktree_governance = data.get("worktree_governance", {})
owners = {e.get("worktree"): e.get("owner_agent_ref") for e in worktree_governance.get("worktree_owners", [])}
delegations = data.get("worktree_delegations", [])

if owner_agent_ref not in agents:
    raise SystemExit(f"unknown owner-agent-ref: {owner_agent_ref}")
if delegated_to_agent_ref not in agents:
    raise SystemExit(f"unknown delegated agent: {delegated_to_agent_ref}")
if owner_agent_ref == delegated_to_agent_ref:
    raise SystemExit("owner and delegated agent must differ")
if worktree not in owners:
    raise SystemExit(f"worktree not found in worktree_owners: {worktree}")
if owners[worktree] != owner_agent_ref:
    raise SystemExit(
        f"owner-agent-ref mismatch for {worktree}: expected {owners[worktree]}, got {owner_agent_ref}"
    )

active = [
    d for d in delegations
    if d.get("worktree") == worktree and d.get("status") == "active"
]

if action == "delegate":
    if active:
        active_ids = ", ".join(d.get("id", "<unknown>") for d in active)
        raise SystemExit(f"worktree {worktree} already has active delegation(s): {active_ids}")
    if delegation_id_arg:
        delegation_id = delegation_id_arg
    else:
        stem = worktree.rstrip("/").split("/")[-1].upper().replace("-", "_")
        target = delegated_to_agent_ref.removeprefix("AGENT_")
        candidate = f"DELEG_{stem}_{target}"
        existing = {d.get("id") for d in delegations}
        idx = 1
        while candidate in existing:
            idx += 1
            candidate = f"DELEG_{stem}_{target}_{idx}"
        delegation_id = candidate
    if not re.fullmatch(r"DELEG_[A-Z0-9_]+", delegation_id):
        raise SystemExit(f"invalid delegation id: {delegation_id}")
    if any(d.get("id") == delegation_id for d in delegations):
        raise SystemExit(f"delegation id already exists: {delegation_id}")

    entry = {
        "id": delegation_id,
        "worktree": worktree,
        "owner_agent_ref": owner_agent_ref,
        "delegated_to_agent_ref": delegated_to_agent_ref,
        "status": "active",
        "commit": commit_sha,
        "notes": notes or f"Delegated effective owner of {worktree} to {delegated_to_agent_ref}.",
    }
    if dry_run:
        print(f"dry-run: would create active delegation {delegation_id}")
        raise SystemExit(0)
    delegations.append(entry)
    data["worktree_delegations"] = delegations
    collab_path.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")
    print(f"created delegation {delegation_id}")
else:
    target = None
    for d in delegations:
        if (
            d.get("worktree") == worktree
            and d.get("owner_agent_ref") == owner_agent_ref
            and d.get("delegated_to_agent_ref") == delegated_to_agent_ref
            and d.get("status") == "active"
        ):
            target = d
            break
    if target is None:
        raise SystemExit(
            f"no active delegation found for {worktree} owner={owner_agent_ref} delegated_to={delegated_to_agent_ref}"
        )
    if dry_run:
        print(f"dry-run: would revoke delegation {target.get('id')}")
        raise SystemExit(0)
    target["status"] = "revoked"
    target["commit"] = commit_sha
    target["notes"] = notes or f"Revoked effective-owner delegation for {worktree} from {delegated_to_agent_ref}."
    data["worktree_delegations"] = delegations
    collab_path.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")
    print(f"revoked delegation {target.get('id')}")
PY

if [[ "${DRY_RUN}" -eq 0 && "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

if [[ "${DRY_RUN}" -eq 0 ]]; then
  ./control-plane/scripts/collab_validate.sh >/dev/null
fi
