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
phase_index = json.loads((root / 'control-plane/views/phase-index.generated.json').read_text(encoding='utf-8'))

errors = []
if phase_index.get('phases') != ledger.get('phases'):
    errors.append('phase-index.generated.json does not match execution-ledger phase structure')

if errors:
    print('execution structure sync check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print('execution structure sync check passed')
PY
