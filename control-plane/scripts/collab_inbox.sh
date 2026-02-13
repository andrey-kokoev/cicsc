#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
MAILBOX_PATH="${ROOT_DIR}/control-plane/views/worktree-mailboxes.generated.json"

WORKTREE=""
ACTIONABLE_ONLY=0
REFRESH=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_inbox.sh --worktree <path> [--actionable-only] [--refresh]

Options:
  --worktree <path>    Absolute worktree path key in mailbox projection.
  --actionable-only    Filter inbox to current_status in {queued, sent}.
  --refresh            Regenerate mailbox projection before reading.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree)
      WORKTREE="${2:-}"
      shift 2
      ;;
    --actionable-only)
      ACTIONABLE_ONLY=1
      shift
      ;;
    --refresh)
      REFRESH=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "unknown option: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

if [[ -z "${WORKTREE}" ]]; then
  echo "--worktree is required" >&2
  usage >&2
  exit 1
fi

cd "${ROOT_DIR}"

if [[ "${REFRESH}" -eq 1 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

python3 - "$MAILBOX_PATH" "$WORKTREE" "$ACTIONABLE_ONLY" <<'PY'
import json
import sys
from pathlib import Path

mailbox_path = Path(sys.argv[1])
worktree = sys.argv[2]
actionable_only = sys.argv[3] == "1"

if not mailbox_path.exists():
    raise SystemExit(f"missing mailbox projection: {mailbox_path}")

data = json.loads(mailbox_path.read_text(encoding="utf-8"))
mailboxes = data.get("mailboxes", {})
entry = mailboxes.get(worktree)
if entry is None:
    print("[]")
    raise SystemExit(0)

inbox = entry.get("inbox", [])
if actionable_only:
    inbox = [m for m in inbox if m.get("current_status") in {"queued", "sent"}]

print(json.dumps(inbox, indent=2))
PY
