#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
COLLAB_PATH="${ROOT_DIR}/control-plane/collaboration/collab-model.yaml"
WARN_HOURS=24
FAIL_HOURS=72
WORKTREE=""
OUT_PATH=""

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_stale_watch.sh [options]

Options:
  --warn-hours <n>      Warn threshold in hours (default: 24).
  --fail-hours <n>      Fail threshold in hours (default: 72).
  --worktree <path>     Optional to-worktree filter.
  --out <path>          Optional JSON report output path.

Semantics:
  Messages whose current status is sent|acknowledged are watched.
  Age is derived from the commit timestamp of the latest message_event.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --warn-hours) WARN_HOURS="${2:-}"; shift 2 ;;
    --fail-hours) FAIL_HOURS="${2:-}"; shift 2 ;;
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --out) OUT_PATH="${2:-}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"

python3 - "$COLLAB_PATH" "$WARN_HOURS" "$FAIL_HOURS" "$WORKTREE" "$OUT_PATH" <<'PY'
import json
import subprocess
import sys
import time
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
warn_hours = int(sys.argv[2])
fail_hours = int(sys.argv[3])
worktree_filter = sys.argv[4]
out_path = sys.argv[5]

collab = yaml.safe_load(collab_path.read_text(encoding="utf-8"))
messages = collab.get("messages", [])
events = collab.get("message_events", [])
events_by_message = {}
for e in events:
    events_by_message.setdefault(e.get("message_ref"), []).append(e)

now = int(time.time())
warn_secs = warn_hours * 3600
fail_secs = fail_hours * 3600

def commit_ts(commit_sha: str) -> int:
    out = subprocess.check_output(
        ["git", "show", "-s", "--format=%ct", commit_sha],
        text=True,
    ).strip()
    return int(out)

watched = []
for m in messages:
    if worktree_filter and m.get("to_worktree") != worktree_filter:
        continue
    evs = sorted(events_by_message.get(m.get("id"), []), key=lambda e: int(e.get("at_seq", 0)))
    if not evs:
        continue
    last = evs[-1]
    status = last.get("to_status")
    if status not in {"sent", "acknowledged"}:
        continue
    c = last.get("commit")
    try:
        ts = commit_ts(c)
    except Exception:
        ts = None
    age_secs = now - ts if ts is not None else None
    severity = "ok"
    if age_secs is None:
        severity = "unknown"
    elif age_secs >= fail_secs:
        severity = "fail"
    elif age_secs >= warn_secs:
        severity = "warn"
    watched.append(
        {
            "message_id": m.get("id"),
            "assignment_ref": m.get("assignment_ref"),
            "to_worktree": m.get("to_worktree"),
            "current_status": status,
            "last_event_commit": c,
            "last_event_timestamp_unix": ts,
            "age_seconds": age_secs,
            "severity": severity,
        }
    )

report = {
    "version": "cicsc/collab-stale-watch-v1",
    "timestamp_unix": now,
    "warn_hours": warn_hours,
    "fail_hours": fail_hours,
    "worktree_filter": worktree_filter or None,
    "watched_count": len(watched),
    "warn_count": sum(1 for w in watched if w["severity"] == "warn"),
    "fail_count": sum(1 for w in watched if w["severity"] == "fail"),
    "rows": watched,
}

if out_path:
    Path(out_path).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

print(json.dumps(report, indent=2))
raise SystemExit(1 if report["fail_count"] > 0 else 0)
PY
