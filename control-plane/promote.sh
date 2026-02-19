#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

USAGE="Usage: $0 [--phase <phase_id>] [--all]"
MODE="all"
PHASE_ID=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --phase)
            PHASE_ID="${2:-}"
            MODE="single"
            shift 2
            ;;
        --all)
            MODE="all"
            shift
            ;;
        --help|-h)
            echo "$USAGE"
            exit 0
            ;;
        *)
            echo "Unknown arg: $1" >&2
            echo "$USAGE" >&2
            exit 1
            ;;
    esac
done

if [[ "$MODE" == "single" && -z "$PHASE_ID" ]]; then
    echo "$USAGE" >&2
    exit 1
fi

python3 - "$MODE" "$PHASE_ID" << 'PY'
import sys
sys.path.insert(0, "control-plane")
from db import get_all_phases, get_phase_checkbox_stats, update_phase_status

mode = sys.argv[1]
phase_id = sys.argv[2]

phases = get_all_phases()
if mode == "single":
    phases = [p for p in phases if p["id"] == phase_id]
    if not phases:
        print(f"ERROR: Phase {phase_id} not found", file=sys.stderr)
        sys.exit(1)

promoted = []
for ph in phases:
    stats = get_phase_checkbox_stats(ph["id"])
    if stats["total"] > 0 and stats["done"] == stats["total"] and ph["status"] != "complete":
        update_phase_status(ph["id"], "complete")
        promoted.append(ph["id"])

if promoted:
    for pid in promoted:
        print(f"Promoted {pid} -> complete")
else:
    print("No eligible phases to promote")
PY
