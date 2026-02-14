#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
REFRESH=0
JSON_MODE=0
STALE_HOURS=24

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_main_status.sh [options]

Options:
  --refresh            Regenerate views before status summary.
  --json               Emit JSON.
  --stale-hours <n>    Threshold for stale acknowledged work (default: 24).
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --refresh) REFRESH=1; shift ;;
    --json) JSON_MODE=1; shift ;;
    --stale-hours) STALE_HOURS="${2:-}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! [[ "${STALE_HOURS}" =~ ^[0-9]+$ ]] || [[ "${STALE_HOURS}" -lt 1 ]]; then
  echo "--stale-hours must be a positive integer" >&2
  exit 1
fi

cd "${ROOT_DIR}"
if [[ "${REFRESH}" -eq 1 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$ROOT_DIR/control-plane/views/worktree-mailboxes.generated.json" "$JSON_MODE" "$STALE_HOURS" <<'PY'
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
mailboxes = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8")).get("mailboxes", {})
json_mode = sys.argv[3] == "1"
stale_hours = int(sys.argv[4])

messages = {m.get("id"): m for m in collab.get("messages", [])}
events_by = {}
for ev in collab.get("message_events", []):
    events_by.setdefault(ev.get("message_ref"), []).append(ev)

summary = {
    "by_worktree": {},
    "totals": {
        "queued": 0,
        "sent": 0,
        "acknowledged": 0,
        "fulfilled": 0,
        "ingested": 0,
        "closed": 0,
        "rescinded": 0,
    },
    "awaiting_main_ingest": [],
    "stale_acknowledged": [],
}

now = datetime.now(timezone.utc)
stale_sec = stale_hours * 3600

for worktree, entry in sorted(mailboxes.items()):
    inbox = entry.get("inbox", [])
    counts = {"queued": 0, "sent": 0, "acknowledged": 0, "fulfilled": 0, "ingested": 0, "closed": 0, "rescinded": 0}
    for item in inbox:
        s = item.get("current_status")
        if s in counts:
            counts[s] += 1
            summary["totals"][s] += 1
        if s in {"fulfilled", "ingested"}:
            summary["awaiting_main_ingest"].append({
                "worktree": worktree,
                "message_id": item.get("id"),
                "assignment_ref": item.get("assignment_ref"),
                "status": s,
            })
        if s == "acknowledged":
            mid = item.get("id")
            evs = sorted(events_by.get(mid, []), key=lambda e: int(e.get("at_seq", 0)))
            if evs:
                at = evs[-1].get("at")
                if at:
                    try:
                        ts = datetime.fromisoformat(at.replace("Z", "+00:00"))
                        age = (now - ts).total_seconds()
                        if age >= stale_sec:
                            summary["stale_acknowledged"].append({
                                "worktree": worktree,
                                "message_id": mid,
                                "assignment_ref": item.get("assignment_ref"),
                                "age_hours": round(age / 3600, 2),
                            })
                    except ValueError:
                        pass
    summary["by_worktree"][worktree] = counts

if json_mode:
    print(json.dumps(summary, indent=2))
    raise SystemExit(0)

print("Main Collaboration Status")
print("By Worktree:")
for wt, counts in summary["by_worktree"].items():
    print(
        f"- {wt}: queued={counts['queued']} sent={counts['sent']} acknowledged={counts['acknowledged']} fulfilled={counts['fulfilled']} ingested={counts['ingested']}"
    )

t = summary["totals"]
print(
    f"Totals: queued={t['queued']} sent={t['sent']} acknowledged={t['acknowledged']} fulfilled={t['fulfilled']} ingested={t['ingested']} closed={t['closed']} rescinded={t['rescinded']}"
)

print("Awaiting Main Ingest:")
if summary["awaiting_main_ingest"]:
    for r in summary["awaiting_main_ingest"]:
        print(f"- {r['message_id']} {r['assignment_ref']} [{r['status']}] @ {r['worktree']}")
else:
    print("- (none)")

print("Stale Acknowledged:")
if summary["stale_acknowledged"]:
    for r in summary["stale_acknowledged"]:
        print(f"- {r['message_id']} {r['assignment_ref']} age={r['age_hours']}h @ {r['worktree']}")
else:
    print("- (none)")
PY
