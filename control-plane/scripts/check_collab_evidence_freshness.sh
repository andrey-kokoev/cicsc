#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

STRICT=0
OUT_PATH=""

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/check_collab_evidence_freshness.sh [options]

Options:
  --strict      Fail when stale/missing evidence is found (default: warn-only).
  --out <path>  Optional JSON report output path.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --strict) STRICT=1; shift ;;
    --out) OUT_PATH="${2:-}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

cd "${ROOT_DIR}"

python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$STRICT" "$OUT_PATH" <<'PY'
import json
import sys
import time
from pathlib import Path
import yaml

collab_path = Path(sys.argv[1])
strict = sys.argv[2] == "1"
out_path = sys.argv[3]
root = Path.cwd()

THRESHOLDS = {
    "EVID_GATE_REPORT": 24 * 3600,
    "EVID_DIFFERENTIAL_LOG": 24 * 3600,
    "EVID_SCRIPT": 7 * 24 * 3600,
    "EVID_THEOREM": 30 * 24 * 3600,
}

collab = yaml.safe_load(collab_path.read_text(encoding="utf-8"))
events = collab.get("message_events", [])
now = int(time.time())

rows = []
stale_count = 0
missing_count = 0
for ev in events:
    for bind in ev.get("evidence_bindings", []):
        kind = bind.get("evidence_kind_ref")
        ref = bind.get("ref")
        if not isinstance(ref, str):
            continue
        path = root / ref
        threshold = THRESHOLDS.get(kind, 24 * 3600)
        if not path.exists():
            missing_count += 1
            rows.append(
                {
                    "message_event_id": ev.get("id"),
                    "evidence_kind_ref": kind,
                    "ref": ref,
                    "status": "missing",
                    "age_seconds": None,
                    "threshold_seconds": threshold,
                }
            )
            continue
        st = path.stat()
        age = max(0, now - int(st.st_mtime))
        status = "stale" if age > threshold else "fresh"
        if status == "stale":
            stale_count += 1
        rows.append(
            {
                "message_event_id": ev.get("id"),
                "evidence_kind_ref": kind,
                "ref": ref,
                "status": status,
                "age_seconds": age,
                "threshold_seconds": threshold,
            }
        )

report = {
    "version": "cicsc/collab-evidence-freshness-v1",
    "timestamp_unix": now,
    "strict_mode": strict,
    "rows_count": len(rows),
    "stale_count": stale_count,
    "missing_count": missing_count,
    "rows": rows,
}

if out_path:
    Path(out_path).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

if stale_count or missing_count:
    print(
        f"collab evidence freshness warning: stale={stale_count} missing={missing_count} "
        f"(strict_mode={strict})",
        file=sys.stderr,
    )
else:
    print("collab evidence freshness check passed")

if strict and (stale_count or missing_count):
    raise SystemExit(1)
raise SystemExit(0)
PY
