#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
source "$ROOT/control-plane/output.sh"

ERRORS=0

echo "Validating execution ledger..."
if ! python3 << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import get_all_checkboxes

errors = []
checkboxes = get_all_checkboxes()
seen = set()

for cb in checkboxes:
    cid = cb["id"]
    if cid in seen:
        errors.append(f"duplicate checkbox: {cid}")
    seen.add(cid)

    status = cb["status"]
    if status not in ("open", "done"):
        errors.append(f"invalid status for {cid}: {status}")

if errors:
    print("  Ledger structure: FAIL", file=sys.stderr)
    for e in errors:
        print(f"  ERROR: {e}", file=sys.stderr)
    raise SystemExit(1)

print(f"  Ledger structure: OK ({len(checkboxes)} checkboxes)")
PY
then
    ERRORS=$((ERRORS + 1))
fi

echo "Validating assignment and agent protocol..."
if ! python3 << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import get_db

conn = get_db()
cur = conn.cursor()

cur.execute("SELECT * FROM checkboxes")
checkboxes = [dict(r) for r in cur.fetchall()]
checkbox_status = {c["id"]: c["status"] for c in checkboxes}

cur.execute("SELECT * FROM assignments")
assignments = [dict(r) for r in cur.fetchall()]

cur.execute("SELECT * FROM agents")
agents = [dict(r) for r in cur.fetchall()]
agent_by_id = {a["id"]: a for a in agents}

errors = []
active_checkboxes = set()
assigned_by_agent = {}

def has_text(v):
    return v is not None and str(v).strip() != ""

for a in assignments:
    cb = a.get("checkbox_ref")
    status = a.get("status")
    agent_ref = a.get("agent_ref")

    if cb not in checkbox_status:
        errors.append(f"invalid checkbox_ref: {cb}")
        continue

    if status not in ("assigned", "done"):
        errors.append(f"invalid status for {cb}: {status}")
        continue

    if agent_ref not in agent_by_id:
        errors.append(f"invalid agent_ref for {cb}: {agent_ref}")

    if status == "assigned":
        if cb in active_checkboxes:
            errors.append(f"multiple active assignments for {cb}")
        active_checkboxes.add(cb)

        if not has_text(a.get("lease_token")):
            errors.append(f"assigned {cb} missing lease_token")
        if not has_text(a.get("lease_expires_at")):
            errors.append(f"assigned {cb} missing lease_expires_at")
        if not has_text(a.get("last_heartbeat_at")):
            errors.append(f"assigned {cb} missing last_heartbeat_at")

        if checkbox_status.get(cb) == "done":
            errors.append(f"checkbox {cb} is done but has active assignment")

        assigned_by_agent[agent_ref] = assigned_by_agent.get(agent_ref, 0) + 1

    if status == "done":
        if checkbox_status.get(cb) != "done":
            errors.append(f"assignment {cb} is done but checkbox is {checkbox_status.get(cb)}")
        if not has_text(a.get("commit_sha")):
            errors.append(f"done assignment {cb} missing commit_sha")
        if not has_text(a.get("completed_at")):
            errors.append(f"done assignment {cb} missing completed_at")

for a in agents:
    aid = a.get("id")
    status = a.get("status")
    blocked_reason = a.get("blocked_reason")
    assigned_count = assigned_by_agent.get(aid, 0)

    if status not in ("standing_by", "busy", "blocked"):
        errors.append(f"invalid agent status for {aid}: {status}")
        continue

    if status == "standing_by" and assigned_count > 0:
        errors.append(f"agent {aid} standing_by with {assigned_count} active assignments")

    if status == "busy" and assigned_count == 0:
        errors.append(f"agent {aid} busy without active assignment")

    if status == "blocked" and not has_text(blocked_reason):
        errors.append(f"agent {aid} blocked without blocked_reason")

for cb in checkboxes:
    cid = cb["id"]
    if cb["status"] == "done" and cid in active_checkboxes:
        errors.append(f"checkbox {cid} is done but has active assignment")

if errors:
    print("  Assignment protocol: FAIL", file=sys.stderr)
    for e in errors:
        print(f"  ERROR: {e}", file=sys.stderr)
    raise SystemExit(1)

print(f"  Assignment protocol: OK ({len(assignments)} assignments, {len(agents)} agents)")
PY
then
    ERRORS=$((ERRORS + 1))
fi

if [[ $ERRORS -eq 0 ]]; then
    echo "Validation passed"
    emit_result ok validate "validation passed"
    exit 0
fi

echo "Validation failed with $ERRORS error(s)" >&2
emit_result error validate "validation failed" "errors=$ERRORS"
exit 1
