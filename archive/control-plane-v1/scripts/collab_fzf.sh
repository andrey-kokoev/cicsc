#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

WORKTREE="${PWD}"
DRY_RUN=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_fzf.sh [--worktree <path>] [--dry-run]
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if ! command -v fzf >/dev/null 2>&1; then
  echo "fzf not found; install fzf or use collab_interactive.sh" >&2
  exit 1
fi

cd "${ROOT_DIR}"
rows="$(
python3 - "$WORKTREE" <<'PY'
import json, subprocess, sys
wt=sys.argv[1]
out=subprocess.check_output(["./control-plane/scripts/collab_inbox.sh","--worktree",wt,"--refresh","--actionable-only"],text=True)
inbox=json.loads(out)
for m in inbox:
    print("\t".join([
        m.get("id",""),
        m.get("assignment_ref",""),
        m.get("current_status",""),
        m.get("branch",""),
    ]))
PY
)"

if [[ -z "${rows}" ]]; then
  echo "no actionable messages for ${WORKTREE}"
  exit 0
fi

picked="$(printf '%s\n' "${rows}" | fzf --delimiter=$'\t' --with-nth=1,2,3,4 --prompt="message> " --preview 'bash -lc "./control-plane/scripts/collab_show_assignment.sh --ref {2} | sed -n \"1,60p\""' --height=80%)"
[[ -n "${picked}" ]] || exit 0
IFS=$'\t' read -r message_ref assignment_ref status branch <<<"${picked}"

script_ref="$(find scripts -maxdepth 1 -type f -name 'check*.sh' | sort | fzf --prompt='script> ' --height=60%)"
[[ -n "${script_ref}" ]] || exit 0

report_ref="$(find docs/pilot -maxdepth 1 -type f -name '*.json' | sort | fzf --prompt='report> ' --height=60%)"
[[ -n "${report_ref}" ]] || exit 0

echo "selected:"
echo "  message=${message_ref}"
echo "  assignment=${assignment_ref}"
echo "  status=${status}"
echo "  branch=${branch}"
echo "  script=${script_ref}"
echo "  report=${report_ref}"

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: no mutation"
  exit 0
fi

if [[ "${status}" == "sent" || "${status}" == "queued" ]]; then
  ./control-plane/scripts/collab_claim_next.sh --worktree "${WORKTREE}" --message-ref "${message_ref}" --checkout-branch
fi

./control-plane/scripts/collab_fulfill.sh \
  --message-ref "${message_ref}" \
  --worktree "${WORKTREE}" \
  --with "${script_ref}" \
  --gate-report "${report_ref}" \
  --auto-commit \
  --suggest-commit
