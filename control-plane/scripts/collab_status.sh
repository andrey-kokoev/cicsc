#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
WORKTREE="${PWD}"
JSON_MODE=0
REFRESH=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_status.sh [options]

Options:
  --worktree <path>   Worktree path key (default: current $PWD).
  --refresh           Regenerate views before computing status.
  --json              Emit JSON instead of text summary.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --refresh) REFRESH=1; shift ;;
    --json) JSON_MODE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"
if [[ "${REFRESH}" -eq 1 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$ROOT_DIR/control-plane/views/worktree-mailboxes.generated.json" "$WORKTREE" "$JSON_MODE" <<'PY'
import json
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
mailboxes = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8")).get("mailboxes", {})
worktree = sys.argv[3]
json_mode = sys.argv[4] == "1"

entry = mailboxes.get(worktree, {"inbox": []})
inbox = entry.get("inbox", [])
assignments = {a.get("id"): a for a in collab.get("assignments", [])}
claim_kinds = {c.get("id"): c for c in collab.get("claim_kinds", [])}
oblig_profiles = {o.get("id"): o for o in collab.get("obligation_profiles", [])}

def enrich(m):
    a = assignments.get(m.get("assignment_ref"), {})
    return {
        "message_id": m.get("id"),
        "assignment_ref": m.get("assignment_ref"),
        "checkbox_ref": a.get("checkbox_ref"),
        "branch": m.get("branch"),
        "status": m.get("current_status"),
    }

ack = [enrich(m) for m in inbox if m.get("current_status") == "acknowledged"]
sent = [enrich(m) for m in inbox if m.get("current_status") in {"sent", "queued"}]
ack.sort(key=lambda r: r["message_id"] or "")
sent.sort(key=lambda r: r["message_id"] or "")

next_action = "idle"
next_detail = ""
if ack:
    first = ack[0]
    next_action = "fulfill_acknowledged_first"
    next_detail = f"fulfill {first['assignment_ref']} ({first['message_id']})"
elif sent:
    first = sent[0]
    next_action = "claim_next_actionable"
    next_detail = f"claim {first['assignment_ref']} ({first['message_id']})"

# Provide lightweight script hints for next action.
script_hints = []
if next_action.startswith("fulfill") and ack:
    a = assignments.get(ack[0]["assignment_ref"], {})
    ck = claim_kinds.get(a.get("claim_kind_ref"), {})
    for pref in ck.get("required_obligation_profile_refs", []):
        p = oblig_profiles.get(pref, {})
        for s in p.get("required_scripts", []):
            script_hints.append(s)

out = {
    "worktree": worktree,
    "in_progress": ack,
    "actionable": sent,
    "next_action": next_action,
    "next_detail": next_detail,
    "script_hints": sorted(set(script_hints)),
}

if json_mode:
    print(json.dumps(out, indent=2, sort_keys=False))
    raise SystemExit(0)

print(f"Worktree: {worktree}")
print("In Progress:")
if ack:
    for r in ack:
        print(f"- {r['checkbox_ref']} {r['assignment_ref']} [{r['status']}] ({r['message_id']})")
else:
    print("- (none)")

print("Actionable:")
if sent:
    for r in sent:
        print(f"- {r['checkbox_ref']} {r['assignment_ref']} [{r['status']}] ({r['message_id']})")
else:
    print("- (none)")

print(f"Next Action: {next_detail if next_detail else 'none'}")
if script_hints:
    print("Script Hints:")
    for s in sorted(set(script_hints)):
        print(f"- {s}")
PY
