#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

CHECKBOX=""
AGENT=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --checkbox) CHECKBOX="$2"; shift 2 ;;
        --agent) AGENT="$2"; shift 2 ;;
        *) echo "Unknown option: $1"; exit 1 ;;
    esac
done

if [[ -z "$CHECKBOX" || -z "$AGENT" ]]; then
    echo "Usage: $0 --checkbox <ref> --agent <ref>"
    exit 1
fi

python3 - "$CHECKBOX" "$AGENT" << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import get_checkbox, get_assignment, create_assignment
from datetime import datetime

checkbox = sys.argv[1]
agent = sys.argv[2]

cb = get_checkbox(checkbox)
if not cb:
    print(f"ERROR: Invalid checkbox: {checkbox}", file=sys.stderr)
    sys.exit(1)

if cb["status"] == "done":
    print(f"ERROR: Checkbox already done: {checkbox}", file=sys.stderr)
    sys.exit(1)

existing = get_assignment(checkbox)
if existing and existing["status"] in ("open", "in_progress"):
    print(f"ERROR: Checkbox already assigned: {checkbox} -> {existing['agent_ref']}", file=sys.stderr)
    sys.exit(1)

create_assignment(checkbox, agent, "open")
print(f"Dispatched {checkbox} -> {agent}")
PY
