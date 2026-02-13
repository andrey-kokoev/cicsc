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
expected = (root / 'control-plane/views/roadmap-structure.generated.md').read_text(encoding='utf-8').splitlines()

phase_re = re.compile(r"^## ([A-Z]{1,2})\. Phase (\d+):\s+(.+)$")
milestone_re = re.compile(r"^### ([A-Z]{1,2}\d+)\.\s+(.+)$")
checkbox_re = re.compile(r"^- \[(x| )\] ([A-Z]{1,2}\d+\.\d+)\s+(.+)$")

exp_phase_re = re.compile(r"^## ([A-Z]{1,2})\. Phase (\d+):\s+(.+)$")
exp_milestone_re = re.compile(r"^### ([A-Z]{1,2}\d+)\.\s+(.+)$")
exp_checkbox_re = re.compile(r"^- ([A-Z]{1,2}\d+\.\d+)\s+(.+)$")


def parse_expected(lines):
    phases = {}
    order = []
    curp = None
    curm = None
    for line in lines:
        m = exp_phase_re.match(line)
        if m:
            key = (m.group(1), int(m.group(2)))
            phases[key] = {"title": m.group(3).strip(), "milestones": [], "milestone_map": {}}
            order.append(key)
            curp = key
            curm = None
            continue
        m = exp_milestone_re.match(line)
        if m and curp:
            mid = m.group(1)
            mt = m.group(2).strip()
            phases[curp]["milestones"].append(mid)
            phases[curp]["milestone_map"][mid] = {"title": mt, "checkboxes": []}
            curm = mid
            continue
        m = exp_checkbox_re.match(line)
        if m and curp and curm:
            phases[curp]["milestone_map"][curm]["checkboxes"].append((m.group(1), m.group(2).strip()))
    return order, phases


def parse_roadmap(lines, expected_phase_keys):
    phases = {}
    curp = None
    curm = None
    for line in lines:
        m = phase_re.match(line)
        if m:
            key = (m.group(1), int(m.group(2)))
            curp = key if key in expected_phase_keys else None
            curm = None
            if curp:
                phases[curp] = {"title": m.group(3).strip(), "milestones": [], "milestone_map": {}}
            continue
        if not curp:
            continue
        m = milestone_re.match(line)
        if m:
            mid = m.group(1)
            mt = m.group(2).strip()
            phases[curp]["milestones"].append(mid)
            phases[curp]["milestone_map"][mid] = {"title": mt, "checkboxes": []}
            curm = mid
            continue
        m = checkbox_re.match(line)
        if m and curm:
            phases[curp]["milestone_map"][curm]["checkboxes"].append((m.group(2), m.group(3).strip()))
    return phases


order, exp = parse_expected(expected)
actual = parse_roadmap(roadmap, set(order))
errors = []

for key in order:
    if key not in actual:
        errors.append(f"missing phase header in ROADMAP.md: {key[0]} Phase {key[1]}")
        continue
    if actual[key]["title"] != exp[key]["title"]:
        errors.append(f"phase title mismatch for {key[0]} Phase {key[1]}: roadmap='{actual[key]['title']}' expected='{exp[key]['title']}'")

    if actual[key]["milestones"] != exp[key]["milestones"]:
        errors.append(
            f"milestone order/id mismatch for {key[0]} Phase {key[1]}: roadmap={actual[key]['milestones']} expected={exp[key]['milestones']}"
        )
        continue

    for mid in exp[key]["milestones"]:
        if actual[key]["milestone_map"][mid]["title"] != exp[key]["milestone_map"][mid]["title"]:
            errors.append(
                f"milestone title mismatch for {mid}: roadmap='{actual[key]['milestone_map'][mid]['title']}' expected='{exp[key]['milestone_map'][mid]['title']}'"
            )
        if actual[key]["milestone_map"][mid]["checkboxes"] != exp[key]["milestone_map"][mid]["checkboxes"]:
            errors.append(
                f"checkbox structure mismatch for {mid}: roadmap={actual[key]['milestone_map'][mid]['checkboxes']} expected={exp[key]['milestone_map'][mid]['checkboxes']}"
            )

if errors:
    print('roadmap structure sync check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print('roadmap structure sync check passed')
PY
