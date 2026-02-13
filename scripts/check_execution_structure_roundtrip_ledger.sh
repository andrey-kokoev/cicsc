#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./control-plane/scripts/generate_views.sh > /dev/null

python3 - <<'PY'
from pathlib import Path
import json
import yaml

root = Path('.')
ledger = yaml.safe_load((root / 'control-plane/execution/execution-ledger.yaml').read_text(encoding='utf-8'))
status = json.loads((root / 'control-plane/views/execution-status.generated.json').read_text(encoding='utf-8'))

rows = status.get('rows', [])
status_by_id = {row['checkbox_id']: row['status'] for row in rows}

errors = []
for phase in ledger.get('phases', []):
    if phase.get('status') == 'planned':
        continue
    for milestone in phase.get('milestones', []):
        for cb in milestone.get('checkboxes', []):
            cid = cb['id']
            if cid not in status_by_id:
                errors.append(f'missing status row for checkbox {cid}')
                continue
            if status_by_id[cid] != cb.get('status'):
                errors.append(
                    f'status mismatch for {cid}: projection={status_by_id[cid]} ledger={cb.get("status")}'
                )

ledger_ids = {
    cb['id']
    for phase in ledger.get('phases', [])
    if phase.get('status') != 'planned'
    for milestone in phase.get('milestones', [])
    for cb in milestone.get('checkboxes', [])
}
unknown = sorted(set(status_by_id.keys()) - ledger_ids)
if unknown:
    errors.append(f'projection includes unknown checkbox ids: {unknown}')

if errors:
    print('execution structure roundtrip (ledger) check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print('execution structure roundtrip (ledger) check passed')
PY
