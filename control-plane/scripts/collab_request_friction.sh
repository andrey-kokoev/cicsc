#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
COLLAB_PATH="${ROOT_DIR}/control-plane/collaboration/collab-model.yaml"

WORKTREE="${PWD}"
FRICTION_TYPE=""
SEVERITY=""
SUMMARY=""
FREQUENCY=""
PROPOSED_FIX=""
NOTES=""
INITIAL_STATUS="sent"
COMMIT_SHA=""
NO_REFRESH=0
DRY_RUN=0
AUTO_COMMIT=0
COMMIT_SUBJECT=""
COMMIT_BODY=()
REPRO_STEPS=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_request_friction.sh [options]

Options:
  --worktree <path>           Worker worktree path (default: $PWD).
  --type <ergonomics|safety|performance|clarity>
  --severity <low|medium|high|critical>
  --summary <text>            Short friction statement.
  --repro-step <text>         Reproduction step (repeatable; at least one required).
  --frequency <text>          Frequency hint (e.g. always, often, occasional).
  --proposed-fix <text>       Optional proposed mitigation.
  --notes <text>              Optional message notes.
  --initial-status <queued|sent>
  --event-commit <sha>        Commit to bind on initial message event (default: HEAD short).
  --commit-sha <sha>          Alias for --event-commit.
  --no-refresh                Do not regenerate views after update.
  --dry-run                   Validate and print planned ids; no mutation.
  --auto-commit               Auto-commit collab model/views after request append.
  --commit-subject <text>     Commit subject override for --auto-commit.
  --message <text>            Alias for --commit-subject.
  --commit-body <text>        Extra commit body line (repeatable).
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --type) FRICTION_TYPE="${2:-}"; shift 2 ;;
    --severity) SEVERITY="${2:-}"; shift 2 ;;
    --summary) SUMMARY="${2:-}"; shift 2 ;;
    --repro-step) REPRO_STEPS+=("${2:-}"); shift 2 ;;
    --frequency) FREQUENCY="${2:-}"; shift 2 ;;
    --proposed-fix) PROPOSED_FIX="${2:-}"; shift 2 ;;
    --notes) NOTES="${2:-}"; shift 2 ;;
    --initial-status) INITIAL_STATUS="${2:-}"; shift 2 ;;
    --event-commit|--commit-sha) COMMIT_SHA="${2:-}"; shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    --auto-commit) AUTO_COMMIT=1; shift ;;
    --commit-subject|--message) COMMIT_SUBJECT="${2:-}"; shift 2 ;;
    --commit-body) COMMIT_BODY+=("${2:-}"); shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${FRICTION_TYPE}" || -z "${SEVERITY}" || -z "${SUMMARY}" ]]; then
  echo "--type, --severity, and --summary are required" >&2
  usage >&2
  exit 1
fi
if [[ ${#REPRO_STEPS[@]} -lt 1 ]]; then
  echo "at least one --repro-step is required" >&2
  usage >&2
  exit 1
fi
if [[ "${INITIAL_STATUS}" != "queued" && "${INITIAL_STATUS}" != "sent" ]]; then
  echo "--initial-status must be queued or sent" >&2
  exit 1
fi

cd "${ROOT_DIR}"
if [[ "${AUTO_COMMIT}" -eq 1 && "${DRY_RUN}" -eq 0 ]]; then
  if [[ -n "$(git status --porcelain)" ]]; then
    echo "auto-commit requires a clean working tree" >&2
    exit 1
  fi
fi

./control-plane/scripts/collab_validate.sh >/dev/null

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

REPRO_JOINED=""
if [[ ${#REPRO_STEPS[@]} -gt 0 ]]; then
  REPRO_JOINED="$(printf '%s\n' "${REPRO_STEPS[@]}")"
fi

_resolved="$({
python3 - "$COLLAB_PATH" "$WORKTREE" "$FRICTION_TYPE" "$SEVERITY" "$SUMMARY" "$FREQUENCY" "$PROPOSED_FIX" "$NOTES" "$INITIAL_STATUS" "$COMMIT_SHA" "$DRY_RUN" "$REPRO_JOINED" <<'PY'
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
worktree = sys.argv[2]
friction_type = sys.argv[3]
severity = sys.argv[4]
summary = sys.argv[5]
frequency = sys.argv[6]
proposed_fix = sys.argv[7]
notes_arg = sys.argv[8]
initial_status = sys.argv[9]
commit_sha = sys.argv[10]
dry_run = sys.argv[11] == "1"
repro_blob = sys.argv[12]

allowed_types = {"ergonomics", "safety", "performance", "clarity"}
allowed_severity = {"low", "medium", "high", "critical"}
if friction_type not in allowed_types:
    raise SystemExit(f"invalid --type: {friction_type}")
if severity not in allowed_severity:
    raise SystemExit(f"invalid --severity: {severity}")
if not re.fullmatch(r"[0-9a-f]{7,40}", commit_sha):
    raise SystemExit(f"invalid commit sha: {commit_sha}")

repro_steps = [x.strip() for x in repro_blob.splitlines() if x.strip()]
if not repro_steps:
    raise SystemExit("at least one repro step is required")

data = yaml.safe_load(collab_path.read_text(encoding="utf-8"))
agents = {a.get("id"): a for a in data.get("agents", [])}
agent = next((a for a in data.get("agents", []) if a.get("worktree") == worktree), None)
if agent is None:
    raise SystemExit(f"no agent mapped to worktree {worktree}")
from_agent_ref = agent.get("id")

friction_policy = data.get("friction_request_policy", {})
kind_ref = friction_policy.get("message_kind_ref")
to_agent_ref = friction_policy.get("triage_authority_agent_ref")
if kind_ref not in {m.get("id") for m in data.get("message_kinds", [])}:
    raise SystemExit(f"friction message kind not declared: {kind_ref}")
if to_agent_ref not in agents:
    raise SystemExit(f"triage authority agent unknown: {to_agent_ref}")

to_worktree = agents[to_agent_ref].get("worktree")

stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
base = f"FRICTION_{from_agent_ref.removeprefix('AGENT_')}_{stamp}"
msg_base = f"MSG_{base}"
existing_msg = {m.get("id") for m in data.get("messages", [])}
message_id = msg_base
i = 1
while message_id in existing_msg:
    i += 1
    message_id = f"{msg_base}_{i}"

event_id = f"MSGEV_{message_id.removeprefix('MSG_')}_{initial_status.upper()}_1"
existing_eids = {e.get("id") for e in data.get("message_events", [])}
if event_id in existing_eids:
    j = 2
    while f"{event_id}_{j}" in existing_eids:
        j += 1
    event_id = f"{event_id}_{j}"

payload_rel = f"control-plane/logs/friction-requests/{message_id}.json"
payload_obj = {
    "message_id": message_id,
    "from_agent_ref": from_agent_ref,
    "from_worktree": worktree,
    "to_agent_ref": to_agent_ref,
    "friction_type": friction_type,
    "severity": severity,
    "summary": summary,
    "repro_steps": repro_steps,
    "frequency": frequency or None,
    "proposed_fix": proposed_fix or None,
    "requested_at": datetime.now(timezone.utc).isoformat(),
    "requested_commit": commit_sha,
}

msg = {
    "id": message_id,
    "kind_ref": kind_ref,
    "assignment_ref": None,
    "from_agent_ref": from_agent_ref,
    "to_agent_ref": to_agent_ref,
    "from_worktree": worktree,
    "to_worktree": to_worktree,
    "branch": "",
    "initial_status": initial_status,
    "payload_refs": [payload_rel],
    "evidence_refs": [],
    "evidence_bindings": [],
    "notes": notes_arg or f"Friction request from {from_agent_ref}",
}

ev = {
    "id": event_id,
    "message_ref": message_id,
    "from_status": None,
    "to_status": initial_status,
    "actor_agent_ref": from_agent_ref,
    "at_seq": 1,
    "commit": commit_sha,
    "evidence_bindings": [],
    "notes": f"Initial friction request dispatch from {from_agent_ref}.",
}

if dry_run:
    print(message_id)
    print(event_id)
    print(payload_rel)
    raise SystemExit(0)

payload_path = collab_path.parents[1] / "logs" / "friction-requests" / f"{message_id}.json"
payload_path.parent.mkdir(parents=True, exist_ok=True)
payload_path.write_text(json.dumps(payload_obj, indent=2) + "\n", encoding="utf-8")

data.setdefault("messages", []).append(msg)
data.setdefault("message_events", []).append(ev)
collab_path.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")

print(message_id)
print(event_id)
print(payload_rel)
PY
} )"

readarray -t _lines <<<"${_resolved}"
MESSAGE_ID="${_lines[0]:-}"
EVENT_ID="${_lines[1]:-}"
PAYLOAD_REF="${_lines[2]:-}"

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: would dispatch friction request ${MESSAGE_ID}"
  echo "dry-run: event ${EVENT_ID}"
  echo "dry-run: payload ${PAYLOAD_REF}"
  exit 0
fi

if [[ "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi
./control-plane/scripts/collab_validate.sh >/dev/null

echo "friction request dispatched: ${MESSAGE_ID}"
echo "payload: ${PAYLOAD_REF}"

if [[ "${AUTO_COMMIT}" -eq 1 ]]; then
  _commit_cmd=(./control-plane/scripts/collab_commit_views.sh --from-last-collab-action)
  if [[ -n "${COMMIT_SUBJECT}" ]]; then
    _commit_cmd+=(--subject "${COMMIT_SUBJECT}")
  fi
  if [[ ${#COMMIT_BODY[@]} -eq 0 ]]; then
    _commit_cmd+=(--body "FrictionType: ${FRICTION_TYPE}" --body "Severity: ${SEVERITY}")
  else
    for line in "${COMMIT_BODY[@]}"; do
      _commit_cmd+=(--body "${line}")
    done
  fi
  "${_commit_cmd[@]}"
  echo "auto-committed collab model/views"
fi
