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
import time
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
assignment_ref = sys.argv[2]
json_mode = sys.argv[3] == "1"
repo_root = Path.cwd()

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
required_script_hints = []
for pref in profile_refs:
    profile = oblig_profiles.get(pref, {})
    required_script_hints.extend(profile.get("required_scripts", []))
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

def recent_files(glob_pattern: str, limit: int = 5):
    out = []
    now = int(time.time())
    for p in repo_root.glob(glob_pattern):
        if not p.is_file():
            continue
        st = p.stat()
        age = max(0, now - int(st.st_mtime))
        out.append(
            {
                "ref": str(p.relative_to(repo_root)),
                "mtime_unix": int(st.st_mtime),
                "age_seconds": age,
            }
        )
    out.sort(key=lambda r: r["mtime_unix"], reverse=True)
    return out[:limit]

candidate_evidence = {
    "EVID_SCRIPT": [],
    "EVID_GATE_REPORT": [],
    "EVID_THEOREM": [],
    "EVID_DIFFERENTIAL_LOG": [],
}

# Scripts: obligation-profile required scripts are strongest hints.
for s in sorted(set(required_script_hints)):
    p = repo_root / s
    if p.exists() and p.is_file():
        st = p.stat()
        candidate_evidence["EVID_SCRIPT"].append(
            {
                "ref": s,
                "mtime_unix": int(st.st_mtime),
                "age_seconds": max(0, int(time.time()) - int(st.st_mtime)),
                "source": "obligation_required_script",
            }
        )

# Reports/logs: recent artifacts in docs/pilot.
candidate_evidence["EVID_GATE_REPORT"] = recent_files("docs/pilot/*.json", limit=8)
candidate_evidence["EVID_DIFFERENTIAL_LOG"] = recent_files("docs/pilot/*.log", limit=8)
candidate_evidence["EVID_THEOREM"] = recent_files("lean/**/*.lean", limit=5)

out = {
    "assignment": assignment,
    "messages": sorted(message_rows, key=lambda r: r["id"]),
    "evidence_counts": evidence_counts,
    "requirements": requirements,
    "candidate_evidence": candidate_evidence,
}

next_step = {"action": "none", "detail": "no further action suggested", "command": ""}
ack_msgs = [m for m in out["messages"] if m["current_status"] == "acknowledged"]
sent_msgs = [m for m in out["messages"] if m["current_status"] in {"sent", "queued"}]
fulfilled_msgs = [m for m in out["messages"] if m["current_status"] == "fulfilled"]
if ack_msgs:
    m = sorted(ack_msgs, key=lambda r: r["id"])[0]
    next_step = {
        "action": "fulfill",
        "detail": f"message {m['id']} is acknowledged and should be fulfilled",
        "command": (
            f"./control-plane/scripts/collab_fulfill.sh --message-ref {m['id']} "
            f"--worktree \"{assignment.get('worktree')}\" --script <path> --gate-report <path>"
        ),
    }
elif sent_msgs:
    m = sorted(sent_msgs, key=lambda r: (r["current_status"] != "sent", r["id"]))[0]
    next_step = {
        "action": "claim",
        "detail": f"message {m['id']} is actionable and should be claimed",
        "command": f"./control-plane/scripts/collab_claim_next.sh --worktree \"{assignment.get('worktree')}\"",
    }
elif fulfilled_msgs:
    m = sorted(fulfilled_msgs, key=lambda r: r["id"])[0]
    next_step = {
        "action": "close_ingested",
        "detail": f"message {m['id']} is fulfilled and should be ingested/closed in main",
        "command": f"./control-plane/scripts/collab_close_ingested.sh --message-ref {m['id']} --commit <sha>",
    }
out["next_step"] = next_step

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
print(f"Next Step: {out['next_step']['detail']}")
if out["next_step"]["command"]:
    print(f"Run: {out['next_step']['command']}")
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
print("")
print("Candidate Evidence Artifacts:")
for kind in ["EVID_SCRIPT", "EVID_GATE_REPORT", "EVID_DIFFERENTIAL_LOG", "EVID_THEOREM"]:
    print(f"- {kind}:")
    rows = out["candidate_evidence"].get(kind, [])
    if not rows:
        print("  - (none)")
        continue
    for r in rows:
        print(f"  - {r['ref']} (age_s={r['age_seconds']})")
PY
