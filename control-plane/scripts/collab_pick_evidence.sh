#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

ASSIGNMENT_REF=""
KIND_FILTER=""
LIMIT=3
JSON_MODE=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_pick_evidence.sh --assignment-ref ASSIGN_... [options]

Options:
  --assignment-ref <id>  Assignment id to inspect.
  --kind <evidence-kind> Restrict suggestions to one evidence kind.
  --limit <n>            Max suggestions per kind (default: 3).
  --json                 Emit JSON instead of text.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --assignment-ref) ASSIGNMENT_REF="${2:-}"; shift 2 ;;
    --kind) KIND_FILTER="${2:-}"; shift 2 ;;
    --limit) LIMIT="${2:-}"; shift 2 ;;
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
if ! [[ "${LIMIT}" =~ ^[0-9]+$ ]] || [[ "${LIMIT}" -lt 1 ]]; then
  echo "--limit must be a positive integer" >&2
  exit 1
fi

cd "${ROOT_DIR}"
assignment_json="$(./control-plane/scripts/collab_show_assignment.sh --ref "${ASSIGNMENT_REF}" --json)"

python3 - "${assignment_json}" "${KIND_FILTER}" "${LIMIT}" "${JSON_MODE}" <<'PY'
import json
import sys

doc = json.loads(sys.argv[1])
kind_filter = sys.argv[2]
limit = int(sys.argv[3])
json_mode = sys.argv[4] == "1"

candidates = doc.get("candidate_evidence", {})
requirements = doc.get("requirements", [])

required_kinds = []
for r in requirements:
    k = r.get("evidence_kind_ref")
    if k and k not in required_kinds:
        required_kinds.append(k)
if not required_kinds:
    required_kinds = list(candidates.keys())

if kind_filter:
    required_kinds = [k for k in required_kinds if k == kind_filter]

def rank(rows):
    def freshness_rank(v):
        return 0 if v.get("freshness") == "fresh" else 1
    return sorted(rows, key=lambda r: (freshness_rank(r), int(r.get("age_seconds", 10**9)), r.get("ref", "")))

out = {"assignment_ref": doc.get("assignment", {}).get("id"), "suggestions": {}}
for kind in required_kinds:
    rows = candidates.get(kind, [])
    out["suggestions"][kind] = rank(rows)[:limit]

if json_mode:
    print(json.dumps(out, indent=2, sort_keys=False))
    raise SystemExit(0)

print(f"Assignment: {out['assignment_ref']}")
for kind, rows in out["suggestions"].items():
    print(f"- {kind}:")
    if not rows:
        print("  - (none)")
        continue
    for r in rows:
        freshness = r.get("freshness", "unknown")
        age = r.get("age_seconds", "n/a")
        print(f"  - {r.get('ref')} (freshness={freshness}, age_s={age})")
PY
