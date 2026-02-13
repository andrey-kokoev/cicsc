#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./control-plane/scripts/generate_views.sh > /dev/null

python3 - <<'PY'
import json
from pathlib import Path
import yaml

root = Path('.')
status = json.loads((root / 'control-plane/views/execution-status.generated.json').read_text(encoding='utf-8'))
ledger = yaml.safe_load((root / 'control-plane/execution/execution-ledger.yaml').read_text(encoding='utf-8'))

rows = status.get('rows', [])
mode = ledger.get('status_source_mode')
status_by_id = {row['checkbox_id']: row['status'] for row in rows}

ledger_ids = set()
ledger_status_by_id = {}
for p in ledger.get('phases', []):
    if p.get('status') == 'planned':
        continue
    for m in p.get('milestones', []):
        for c in m.get('checkboxes', []):
            cid = c['id']
            ledger_ids.add(cid)
            ledger_status_by_id[cid] = c.get('status')

projection_ids = set(status_by_id.keys())
missing = sorted(ledger_ids - projection_ids)
unknown = sorted(projection_ids - ledger_ids)

errors = []
if missing:
    errors.append(f"missing statuses for ledger checkbox ids: {missing}")
if unknown:
    errors.append(f"unknown projection checkbox ids not in ledger scope: {unknown}")

if mode == 'execution_ledger_yaml_canonical':
    mismatches = []
    for cid in sorted(ledger_ids & projection_ids):
        ls = ledger_status_by_id.get(cid)
        ps = status_by_id.get(cid)
        if ls != ps:
            mismatches.append((cid, ls, ps))
    if mismatches:
        errors.append(f"status mismatches (ledger vs projection): {mismatches}")

if errors:
    print('status projection sync (ledger) check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print(f'status projection sync (ledger) check passed ({mode})')
PY
