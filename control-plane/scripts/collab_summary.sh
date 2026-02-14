#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"
SINCE=""
JSON_MODE=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_summary.sh --worktree <path> [--since <iso-date>] [--json]
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --since) SINCE="${2:-}"; shift 2 ;;
    --json) JSON_MODE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"

python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$WORKTREE" "$SINCE" "$JSON_MODE" <<'PY'
import datetime as dt
import json
import subprocess
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
worktree = sys.argv[2]
since_raw = sys.argv[3]
json_mode = sys.argv[4] == "1"

agents = collab.get("agents", [])
agent = next((a for a in agents if a.get("worktree") == worktree), None)
if agent is None:
    raise SystemExit(f"unknown worktree: {worktree}")
agent_ref = agent.get("id")

since_ts = 0
if since_raw:
    try:
        since_ts = int(dt.datetime.fromisoformat(since_raw).timestamp())
    except Exception as exc:
        raise SystemExit(f"invalid --since value '{since_raw}': {exc}")

def commit_ts(sha: str) -> int:
    out = subprocess.check_output(["git", "show", "-s", "--format=%ct", sha], text=True).strip()
    return int(out)

assignments = {a.get("id"): a for a in collab.get("assignments", []) if a.get("agent_ref") == agent_ref}
messages = [m for m in collab.get("messages", []) if m.get("to_worktree") == worktree]
events = collab.get("message_events", [])
events_by_message = {}
for ev in events:
    events_by_message.setdefault(ev.get("message_ref"), []).append(ev)

fulfilled_assignments = []
commit_set = set()
script_counter = {}
durations = []

for m in messages:
    aref = m.get("assignment_ref")
    if aref not in assignments:
        continue
    evs = sorted(events_by_message.get(m.get("id"), []), key=lambda e: int(e.get("at_seq", 0)))
    if not evs:
        continue
    terminal = evs[-1].get("to_status")
    if terminal not in {"fulfilled", "ingested", "closed"}:
        continue

    fulfilled_event = next((e for e in evs if e.get("to_status") == "fulfilled" and e.get("actor_agent_ref") == agent_ref), None)
    if fulfilled_event is None:
        continue
    fts = commit_ts(fulfilled_event.get("commit"))
    if fts < since_ts:
        continue
    fulfilled_assignments.append(aref)

    for ev in evs:
        if ev.get("actor_agent_ref") != agent_ref:
            continue
        try:
            ts = commit_ts(ev.get("commit"))
        except Exception:
            continue
        if ts >= since_ts:
            commit_set.add(ev.get("commit"))
        for bind in ev.get("evidence_bindings", []):
            if bind.get("evidence_kind_ref") == "EVID_SCRIPT":
                script_counter[bind.get("ref")] = script_counter.get(bind.get("ref"), 0) + 1

    ack_event = next((e for e in evs if e.get("to_status") == "acknowledged"), None)
    if ack_event:
        try:
            ats = commit_ts(ack_event.get("commit"))
            if ats >= since_ts:
                durations.append(max(0, fts - ats))
        except Exception:
            pass

avg_secs = int(sum(durations) / len(durations)) if durations else 0
out = {
    "worktree": worktree,
    "agent_ref": agent_ref,
    "since": since_raw or None,
    "fulfilled_assignments": sorted(set(fulfilled_assignments)),
    "fulfilled_count": len(set(fulfilled_assignments)),
    "commit_count": len(commit_set),
    "average_seconds_per_assignment": avg_secs,
    "script_usage": dict(sorted(script_counter.items(), key=lambda kv: (-kv[1], kv[0]))),
}

if json_mode:
    print(json.dumps(out, indent=2))
    raise SystemExit(0)

print(f"{worktree} summary ({since_raw or 'all time'}):")
print(f"- assignments fulfilled: {out['fulfilled_count']}")
print(f"- commits referenced: {out['commit_count']}")
print(f"- average time per assignment: {out['average_seconds_per_assignment']}s")
if out["script_usage"]:
    print("- evidence scripts used:")
    for k, v in out["script_usage"].items():
        print(f"  - {k} ({v}x)")
else:
    print("- evidence scripts used: (none)")
PY
