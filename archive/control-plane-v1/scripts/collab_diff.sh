#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

ASSIGNMENT_REF=""
JSON_MODE=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_diff.sh --assignment-ref ASSIGN_... [--json]
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --assignment-ref) ASSIGNMENT_REF="${2:-}"; shift 2 ;;
    --json) JSON_MODE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${ASSIGNMENT_REF}" ]]; then
  echo "--assignment-ref is required" >&2
  usage >&2
  exit 1
fi

cd "${ROOT_DIR}"

python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$ASSIGNMENT_REF" "$JSON_MODE" <<'PY'
import json
import subprocess
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
assignment_ref = sys.argv[2]
json_mode = sys.argv[3] == "1"

assignments = {a.get("id"): a for a in collab.get("assignments", [])}
messages = collab.get("messages", [])
events = collab.get("message_events", [])

assignment = assignments.get(assignment_ref)
if assignment is None:
    raise SystemExit(f"assignment not found: {assignment_ref}")

msg_ids = [m.get("id") for m in messages if m.get("assignment_ref") == assignment_ref]
evs = [e for e in events if e.get("message_ref") in msg_ids]
evs = sorted(evs, key=lambda e: int(e.get("at_seq", 0)))
if not evs:
    raise SystemExit(f"no events for assignment: {assignment_ref}")

claim_ev = next((e for e in evs if e.get("to_status") == "acknowledged"), evs[0])
claim_seq = int(claim_ev.get("at_seq", 0))

post = [e for e in evs if int(e.get("at_seq", 0)) >= claim_seq]
commit_order = []
seen = set()
for e in post:
    c = e.get("commit")
    if c and c not in seen:
        seen.add(c)
        commit_order.append(c)

files = set()
for c in commit_order:
    try:
        out = subprocess.check_output(["git", "show", "--name-only", "--pretty=format:", c], text=True)
    except Exception:
        continue
    for line in out.splitlines():
        line = line.strip()
        if line:
            files.add(line)

evidence = []
for e in post:
    for b in e.get("evidence_bindings", []):
        evidence.append(
            {
                "message_event_id": e.get("id"),
                "evidence_kind_ref": b.get("evidence_kind_ref"),
                "ref": b.get("ref"),
                "commit": b.get("commit"),
            }
        )

out = {
    "assignment_ref": assignment_ref,
    "checkbox_ref": assignment.get("checkbox_ref"),
    "branch": assignment.get("branch"),
    "commits_since_claim": commit_order,
    "files_modified": sorted(files),
    "evidence_generated": evidence,
}

if json_mode:
    print(json.dumps(out, indent=2))
    raise SystemExit(0)

print(f"Assignment: {assignment_ref}")
print(f"Checkbox: {out['checkbox_ref']}")
print(f"Branch: {out['branch']}")
print("Commits since claim:")
if out["commits_since_claim"]:
    for c in out["commits_since_claim"]:
        print(f"- {c}")
else:
    print("- (none)")
print("Files modified:")
if out["files_modified"]:
    for f in out["files_modified"]:
        print(f"- {f}")
else:
    print("- (none)")
print("Evidence generated:")
if out["evidence_generated"]:
    for e in out["evidence_generated"]:
        print(f"- {e['evidence_kind_ref']} {e['ref']} @ {e['commit']}")
else:
    print("- (none)")
PY
