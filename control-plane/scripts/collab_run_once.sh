#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
WORKTREE="${PWD}"
MESSAGE_REF=""
COMMIT_SHA=""

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_run_once.sh [options]

Options:
  --worktree <path>     Worktree path key (default: current $PWD).
  --message-ref <id>    Explicit message to process (otherwise first actionable).
  --commit <sha>        Commit for acknowledge event (default: current HEAD short).

Behavior:
  1) Regenerate mailbox view
  2) Claim next actionable message (or explicit message)
  3) Print fulfillment guidance derived from obligation profile
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --message-ref) MESSAGE_REF="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

if [[ -n "${MESSAGE_REF}" ]]; then
  ./control-plane/scripts/collab_claim_next.sh \
    --worktree "${WORKTREE}" \
    --message-ref "${MESSAGE_REF}" \
    --commit "${COMMIT_SHA}" >/dev/null
else
  ./control-plane/scripts/collab_claim_next.sh \
    --worktree "${WORKTREE}" \
    --commit "${COMMIT_SHA}" >/dev/null
fi

python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$WORKTREE" "$MESSAGE_REF" <<'PY'
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
worktree = sys.argv[2]
explicit_ref = sys.argv[3] if len(sys.argv) > 3 else ""

agents = {a.get("id"): a for a in collab.get("agents", [])}
agent = next((a for a in collab.get("agents", []) if a.get("worktree") == worktree), None)
if agent is None:
    raise SystemExit(f"no agent mapped to worktree {worktree}")

events = collab.get("message_events", [])
events_by_message = {}
for e in events:
    events_by_message.setdefault(e.get("message_ref"), []).append(e)

messages = collab.get("messages", [])
current = []
for m in messages:
    evs = sorted(events_by_message.get(m.get("id"), []), key=lambda e: int(e.get("at_seq", 0)))
    if not evs:
        continue
    current_status = evs[-1].get("to_status")
    current.append((m, current_status))

target = None
if explicit_ref:
    for m, status in current:
        if m.get("id") == explicit_ref:
            target = (m, status)
            break
else:
    candidates = [x for x in current if x[0].get("to_worktree") == worktree and x[1] in {"acknowledged", "sent", "queued"}]
    candidates.sort(key=lambda x: x[0].get("id", ""))
    for m, status in candidates:
        if status == "acknowledged":
            target = (m, status)
            break
    if target is None and candidates:
        target = candidates[0]

if target is None:
    print("No actionable message currently owned by this worktree.")
    raise SystemExit(0)

m, status = target
assignments = {a.get("id"): a for a in collab.get("assignments", [])}
claim_kinds = {c.get("id"): c for c in collab.get("claim_kinds", [])}
oblig_profiles = {o.get("id"): o for o in collab.get("obligation_profiles", [])}

assignment = assignments.get(m.get("assignment_ref"))
if assignment is None:
    raise SystemExit(f"assignment not found for message {m.get('id')}")

claim_kind_ref = assignment.get("claim_kind_ref")
claim_kind = claim_kinds.get(claim_kind_ref, {})
profile_refs = claim_kind.get("required_obligation_profile_refs", [])

print(f"Claimed message: {m.get('id')}")
print(f"Assignment: {assignment.get('id')} ({assignment.get('checkbox_ref')})")
print(f"Claim kind: {claim_kind_ref}")
print(f"Current status: {status}")
print("")
print("Fulfillment requirements:")
for pref in profile_refs:
    p = oblig_profiles.get(pref)
    if not p:
        continue
    print(f"- Obligation profile: {pref}")
    for ev in p.get("required_evidence", []):
        print(f"  - evidence: {ev.get('evidence_kind_ref')} (min {ev.get('min_count')})")
    for s in p.get("required_scripts", []):
        print(f"  - script hint: {s}")
print("")
print("Next command template:")
print(
    "  ./control-plane/scripts/collab_fulfill.sh "
    f"--message-ref {m.get('id')} --worktree \"{worktree}\" "
    "--script <script-path> --gate-report <report-path>"
)
PY
