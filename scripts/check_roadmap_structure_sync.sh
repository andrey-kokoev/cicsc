#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

./control-plane/scripts/generate_views.sh > /dev/null

python3 - <<'PY'
from pathlib import Path
import re

root = Path('.')
roadmap = (root / 'ROADMAP.md').read_text(encoding='utf-8').splitlines()
expected_md = (root / 'control-plane/views/roadmap-structure.generated.md').read_text(encoding='utf-8').splitlines()

roadmap_phase_re = re.compile(r"^## ([A-Z]{1,2})\. Phase (\d+):\s+(.+)$")
expected_row_re = re.compile(r"^\| ([A-Z]{1,2}) \| (\d+) \| (.+) \| (\w+) \|$")

roadmap_map = {}
for line in roadmap:
    m = roadmap_phase_re.match(line)
    if m:
        roadmap_map[(m.group(1), int(m.group(2)))] = m.group(3).strip()

errors = []
for line in expected_md:
    m = expected_row_re.match(line)
    if not m:
        continue
    pid, num, title, _status = m.group(1), int(m.group(2)), m.group(3).strip(), m.group(4)
    if (pid, num) not in roadmap_map:
        errors.append(f"missing phase header in ROADMAP.md: {pid} Phase {num}")
        continue
    if roadmap_map[(pid, num)] != title:
        errors.append(
            f"phase title mismatch for {pid} Phase {num}: roadmap='{roadmap_map[(pid, num)]}' expected='{title}'"
        )

if errors:
    print('roadmap structure sync check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print('roadmap structure sync check passed')
PY
