#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
ASSIGNMENT_REF=""
JSON_MODE=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_show_assignment.sh --ref ASSIGN_... [options]

Options:
  --ref <id>      Assignment id to inspect.
  --json          Emit JSON instead of text.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --ref) ASSIGNMENT_REF="${2:-}"; shift 2 ;;
    --json) JSON_MODE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${ASSIGNMENT_REF}" ]]; then
  echo "--ref is required" >&2
  usage >&2
  exit 1
fi

cd "${ROOT_DIR}"

python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$ASSIGNMENT_REF" "$JSON_MODE" <<'PY'
import json
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
assignment_ref = sys.argv[2]
json_mode = sys.argv[3] == "1"

assignments = {a.get("id"): a for a in collab.get("assignments", [])}
messages = collab.get("messages", [])
events = collab.get("message_events", [])
claim_kinds = {c.get("id"): c for c in collab.get("claim_kinds", [])}
oblig_profiles = {o.get("id"): o for o in collab.get("obligation_profiles", [])}

assignment = assignments.get(assignment_ref)
if assignment is None:
    raise SystemExit(f"assignment not found: {assignment_ref}")

msgs = [m for m in messages if m.get("assignment_ref") == assignment_ref]
events_by_msg = {}
for e in events:
    events_by_msg.setdefault(e.get("message_ref"), []).append(e)

message_rows = []
evidence_counts = {}
for m in msgs:
    mid = m.get("id")
    evs = sorted(events_by_msg.get(mid, []), key=lambda e: int(e.get("at_seq", 0)))
    current = evs[-1].get("to_status") if evs else m.get("initial_status")
    message_rows.append(
        {
            "id": mid,
            "branch": m.get("branch"),
            "current_status": current,
            "event_count": len(evs),
        }
    )
    for ev in evs:
        if ev.get("to_status") != "fulfilled":
            continue
        if ev.get("actor_agent_ref") != assignment.get("agent_ref"):
            continue
        for bind in ev.get("evidence_bindings", []):
            kind = bind.get("evidence_kind_ref")
            evidence_counts[kind] = evidence_counts.get(kind, 0) + 1

claim_kind = claim_kinds.get(assignment.get("claim_kind_ref"), {})
profile_refs = claim_kind.get("required_obligation_profile_refs", [])
requirements = []
for pref in profile_refs:
    profile = oblig_profiles.get(pref, {})
    for req in profile.get("required_evidence", []):
        kind = req.get("evidence_kind_ref")
        need = int(req.get("min_count", 0))
        have = int(evidence_counts.get(kind, 0))
        requirements.append(
            {
                "profile_ref": pref,
                "evidence_kind_ref": kind,
                "required_min": need,
                "have": have,
                "missing": max(0, need - have),
            }
        )

out = {
    "assignment": assignment,
    "messages": sorted(message_rows, key=lambda r: r["id"]),
    "evidence_counts": evidence_counts,
    "requirements": requirements,
}

if json_mode:
    print(json.dumps(out, indent=2, sort_keys=False))
    raise SystemExit(0)

print(f"Assignment: {assignment_ref}")
print(f"Checkbox: {assignment.get('checkbox_ref')}")
print(f"Agent: {assignment.get('agent_ref')}")
print(f"Worktree: {assignment.get('worktree')}")
print(f"Branch: {assignment.get('branch')}")
print(f"Status/Outcome: {assignment.get('status')} / {assignment.get('outcome')}")
print("")
print("Messages:")
for r in out["messages"]:
    print(f"- {r['id']} [{r['current_status']}] events={r['event_count']} branch={r['branch']}")
print("")
print("Evidence Counts (fulfilled by assignee):")
if out["evidence_counts"]:
    for k, v in sorted(out["evidence_counts"].items()):
        print(f"- {k}: {v}")
else:
    print("- (none)")
print("")
print("Requirement Delta:")
if out["requirements"]:
    for r in out["requirements"]:
        print(
            f"- {r['profile_ref']} {r['evidence_kind_ref']}: have {r['have']}, "
            f"need {r['required_min']}, missing {r['missing']}"
        )
else:
    print("- (no declared obligation requirements)")
PY
