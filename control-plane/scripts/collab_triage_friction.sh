#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
COLLAB_PATH="${ROOT_DIR}/control-plane/collaboration/collab-model.yaml"

MESSAGE_REF=""
DECISION=""
NOTES=""
BACKLOG_REF=""
COMMIT_SHA=""
NO_REFRESH=0
DRY_RUN=0
AUTO_COMMIT=0
COMMIT_SUBJECT=""
COMMIT_BODY=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_triage_friction.sh [options]

Options:
  --message-ref <MSG_...>     Friction request message id.
  --decision <accept_now|accept_later|reject>
  --notes <text>              Optional triage rationale.
  --backlog-ref <id>          Optional backlog/phase reference for accept_later.
  --event-commit <sha>        Commit to bind on triage events (default: HEAD short).
  --commit-sha <sha>          Alias for --event-commit.
  --no-refresh                Do not regenerate views after triage.
  --dry-run                   Validate and print planned transitions.
  --auto-commit               Auto-commit collab model/views after triage.
  --commit-subject <text>     Commit subject override for --auto-commit.
  --message <text>            Alias for --commit-subject.
  --commit-body <text>        Extra commit body line (repeatable).
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --message-ref) MESSAGE_REF="${2:-}"; shift 2 ;;
    --decision) DECISION="${2:-}"; shift 2 ;;
    --notes) NOTES="${2:-}"; shift 2 ;;
    --backlog-ref) BACKLOG_REF="${2:-}"; shift 2 ;;
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

if [[ -z "${MESSAGE_REF}" || -z "${DECISION}" ]]; then
  echo "--message-ref and --decision are required" >&2
  usage >&2
  exit 1
fi
if [[ "${DECISION}" != "accept_now" && "${DECISION}" != "accept_later" && "${DECISION}" != "reject" ]]; then
  echo "--decision must be accept_now, accept_later, or reject" >&2
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

_resolved="$({
python3 - "$COLLAB_PATH" "$MESSAGE_REF" "$DECISION" "$NOTES" "$BACKLOG_REF" "$COMMIT_SHA" "$DRY_RUN" <<'PY'
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
message_ref = sys.argv[2]
decision = sys.argv[3]
notes = sys.argv[4]
backlog_ref = sys.argv[5]
commit_sha = sys.argv[6]
dry_run = sys.argv[7] == "1"

if not re.fullmatch(r"[0-9a-f]{7,40}", commit_sha):
    raise SystemExit(f"invalid commit sha: {commit_sha}")

data = yaml.safe_load(collab_path.read_text(encoding="utf-8"))
messages = {m.get("id"): m for m in data.get("messages", [])}
if message_ref not in messages:
    raise SystemExit(f"unknown message_ref: {message_ref}")

msg = messages[message_ref]
policy = data.get("friction_request_policy", {})
kind_ref = policy.get("message_kind_ref")
triage_agent = policy.get("triage_authority_agent_ref")
if msg.get("kind_ref") != kind_ref:
    raise SystemExit(f"message {message_ref} is not friction kind {kind_ref}")

events = [e for e in data.get("message_events", []) if e.get("message_ref") == message_ref]
if not events:
    raise SystemExit(f"message {message_ref} has no lifecycle events")
events = sorted(events, key=lambda e: int(e.get("at_seq", 0)))
current = events[-1].get("to_status")
if current in {"closed", "rejected", "rescinded"}:
    raise SystemExit(f"message {message_ref} already terminal: {current}")

plan = []
if current == "queued":
    plan.append("sent")
    plan.append("acknowledged")
elif current == "sent":
    plan.append("acknowledged")
elif current == "acknowledged":
    pass
else:
    raise SystemExit(f"unsupported current status for triage: {current}")

if decision == "reject":
    final_status = "rejected"
else:
    final_status = "closed"
plan.append(final_status)

report_rel = f"control-plane/logs/friction-triage/{message_ref}.json"
report_abs = collab_path.parents[1] / "logs" / "friction-triage" / f"{message_ref}.json"

report = {
    "message_ref": message_ref,
    "decision": decision,
    "current_status_before": current,
    "planned_transitions": plan,
    "triage_agent_ref": triage_agent,
    "triaged_at": datetime.now(timezone.utc).isoformat(),
    "commit": commit_sha,
    "notes": notes or None,
    "backlog_ref": backlog_ref or None,
}

if not dry_run:
    report_abs.parent.mkdir(parents=True, exist_ok=True)
    report_abs.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

print(triage_agent)
print(report_rel)
print(current)
for st in plan:
    print(st)
PY
} )"

readarray -t _lines <<<"${_resolved}"
TRIAGE_AGENT="${_lines[0]:-}"
REPORT_REF="${_lines[1]:-}"
CURRENT_STATUS="${_lines[2]:-}"
TRANSITIONS=("${_lines[@]:3}")

if [[ ${#TRANSITIONS[@]} -eq 0 ]]; then
  echo "no transitions planned" >&2
  exit 1
fi

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: would triage ${MESSAGE_REF} from ${CURRENT_STATUS} with decision ${DECISION}"
  printf 'dry-run: transitions: %s\n' "${TRANSITIONS[*]}"
  echo "dry-run: triage report ${REPORT_REF}"
  exit 0
fi

DIGEST="sha256:$(sha256sum "${REPORT_REF}" | awk '{print $1}')"
EVID_ITEM="${REPORT_REF}|EVID_GATE_REPORT|${COMMIT_SHA}|${DIGEST}"

for st in "${TRANSITIONS[@]}"; do
  note="friction triage decision=${DECISION}"
  if [[ -n "${NOTES}" ]]; then
    note="${note}; notes=${NOTES}"
  fi
  if [[ -n "${BACKLOG_REF}" ]]; then
    note="${note}; backlog_ref=${BACKLOG_REF}"
  fi

  if [[ "${st}" == "closed" || "${st}" == "rejected" ]]; then
    ./control-plane/scripts/collab_append_event.sh \
      --message-ref "${MESSAGE_REF}" \
      --to-status "${st}" \
      --actor-agent-ref "${TRIAGE_AGENT}" \
      --commit "${COMMIT_SHA}" \
      --notes "${note}" \
      --evidence "${EVID_ITEM}" \
      --no-refresh
  else
    ./control-plane/scripts/collab_append_event.sh \
      --message-ref "${MESSAGE_REF}" \
      --to-status "${st}" \
      --actor-agent-ref "${TRIAGE_AGENT}" \
      --commit "${COMMIT_SHA}" \
      --notes "${note}" \
      --no-refresh
  fi

done

if [[ "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi
./control-plane/scripts/collab_validate.sh >/dev/null

echo "triaged friction request: ${MESSAGE_REF}"
echo "decision: ${DECISION}"
echo "report: ${REPORT_REF}"

if [[ "${AUTO_COMMIT}" -eq 1 ]]; then
  _commit_cmd=(./control-plane/scripts/collab_commit_views.sh --from-last-collab-action)
  if [[ -n "${COMMIT_SUBJECT}" ]]; then
    _commit_cmd+=(--subject "${COMMIT_SUBJECT}")
  fi
  if [[ ${#COMMIT_BODY[@]} -eq 0 ]]; then
    _commit_cmd+=(--body "Decision: ${DECISION}" --body "FrictionMessage: ${MESSAGE_REF}")
  else
    for line in "${COMMIT_BODY[@]}"; do
      _commit_cmd+=(--body "${line}")
    done
  fi
  "${_commit_cmd[@]}"
  echo "auto-committed collab model/views"
fi
