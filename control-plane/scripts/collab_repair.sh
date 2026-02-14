#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

AUTO_COMMIT=0
DRY_RUN=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_repair.sh [options]

Options:
  --auto-commit    Automatically commit repairs
  --dry-run        Show what would be repaired without making changes
  -h, --help       Show this message
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --auto-commit) AUTO_COMMIT=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"

echo "collab-repair: analyzing..."

REPAIRS=0

# Find illegal fulfill events
echo "checking for illegal fulfill events..."
python3 <<'PY'
import yaml
import sys
from pathlib import Path

doc = yaml.safe_load(Path("control-plane/collaboration/collab-model.yaml").read_text(encoding="utf-8"))

invalid = []
for e in doc.get("message_events", []):
    if e.get("to_status") == "fulfilled" and e.get("from_status") != "acknowledged":
        invalid.append(e.get("id"))

for eid in invalid:
    print(f"INVALID:{eid}")
PY
