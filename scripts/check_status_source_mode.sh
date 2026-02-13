#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
from pathlib import Path
import yaml

root = Path('.')
cfg = yaml.safe_load((root / 'control-plane/execution/execution-ledger.yaml').read_text(encoding='utf-8'))
mode = cfg.get('status_source_mode')

if mode != 'roadmap_md_canonical':
    print('status source mode check failed')
    print(f'- unsupported status_source_mode during bootstrap: {mode}')
    print('- expected: roadmap_md_canonical')
    raise SystemExit(1)

print('status source mode check passed')
PY
