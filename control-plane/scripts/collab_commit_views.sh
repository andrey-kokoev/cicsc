#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
SUBJECT="governance/collab: commit model and generated views"
BODY=()
DRY_RUN=0
NO_REFRESH=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_commit_views.sh [options]

Options:
  --subject <text>    Commit subject (default provided).
  --body <text>       Additional commit body line (repeatable).
  --no-refresh        Do not run generate_views before staging.
  --dry-run           Show staged files and commit command, do not commit.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --subject) SUBJECT="${2:-}"; shift 2 ;;
    --body) BODY+=("${2:-}"); shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"

if [[ "${NO_REFRESH}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null
fi

./control-plane/scripts/collab_validate.sh >/dev/null

staged=()
if [[ -f control-plane/collaboration/collab-model.yaml ]]; then
  staged+=("control-plane/collaboration/collab-model.yaml")
fi

while IFS= read -r f; do
  staged+=("$f")
done < <(git ls-files 'control-plane/views/*.generated.*')

if [[ ${#staged[@]} -eq 0 ]]; then
  echo "no collab/view files configured for staging" >&2
  exit 1
fi

git add "${staged[@]}"

if git diff --cached --quiet; then
  echo "nothing to commit (collab model/views unchanged)"
  exit 0
fi

if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: would commit with subject:"
  echo "  ${SUBJECT}"
  echo "dry-run: staged files:"
  git diff --cached --name-only
  exit 0
fi

cmd=(git commit -m "${SUBJECT}")
for line in "${BODY[@]}"; do
  cmd+=(-m "${line}")
done
"${cmd[@]}"
