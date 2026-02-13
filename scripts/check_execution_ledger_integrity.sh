#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

python3 - <<'PY'
from pathlib import Path
import re
import yaml

root = Path('.')
ledger = yaml.safe_load((root / 'control-plane/execution/execution-ledger.yaml').read_text(encoding='utf-8'))

phase_id_re = re.compile(r'^[A-Z]{1,2}$')
milestone_id_re = re.compile(r'^([A-Z]{1,2})(\d+)$')
checkbox_id_re = re.compile(r'^([A-Z]{1,2})(\d+)\.(\d+)$')

errors = []
phases = ledger.get('phases', [])
if not phases:
    errors.append('execution-ledger has no phases')

prev_no = None
seen_phase_ids = set()
seen_phase_nos = set()

for phase in phases:
    pid = phase.get('id')
    pno = phase.get('number')
    title = phase.get('title')

    if not isinstance(pid, str) or not phase_id_re.match(pid):
        errors.append(f'invalid phase id: {pid}')
    if pid in seen_phase_ids:
        errors.append(f'duplicate phase id: {pid}')
    seen_phase_ids.add(pid)

    if not isinstance(pno, int) or pno < 1:
        errors.append(f'invalid phase number for {pid}: {pno}')
    if pno in seen_phase_nos:
        errors.append(f'duplicate phase number: {pno}')
    seen_phase_nos.add(pno)
    if prev_no is not None and pno != prev_no + 1:
        errors.append(f'phase numbering not linear: got Phase {pno} after Phase {prev_no}')
    prev_no = pno

    if not title:
        errors.append(f'missing phase title for {pid}')

    milestones = phase.get('milestones', [])
    if not milestones:
        errors.append(f'phase {pid} has zero milestones')
        continue

    prev_milestone_no = None
    seen_milestones = set()
    for m in milestones:
        mid = m.get('id')
        mt = m.get('title')
        mm = milestone_id_re.match(mid or '')
        if not mm:
            errors.append(f'invalid milestone id: {mid}')
            continue
        mcode, mnum_s = mm.group(1), mm.group(2)
        mnum = int(mnum_s)
        if mcode != pid:
            errors.append(f'milestone {mid} not in phase {pid}')
        if mid in seen_milestones:
            errors.append(f'duplicate milestone id in phase {pid}: {mid}')
        seen_milestones.add(mid)
        if prev_milestone_no is not None and mnum < prev_milestone_no:
            errors.append(f'milestone order regressed in {pid}: {mnum} after {prev_milestone_no}')
        prev_milestone_no = mnum
        if not mt:
            errors.append(f'missing milestone title: {mid}')

        checkboxes = m.get('checkboxes', [])
        if not checkboxes:
            errors.append(f'milestone {mid} has zero checkboxes')
            continue

        prev_item = None
        seen_checkbox = set()
        for c in checkboxes:
            cid = c.get('id')
            ct = c.get('title')
            status = c.get('status')
            cm = checkbox_id_re.match(cid or '')
            if not cm:
                errors.append(f'invalid checkbox id: {cid}')
                continue
            ccode, cmnum_s, citem_s = cm.group(1), cm.group(2), cm.group(3)
            cmnum = int(cmnum_s)
            citem = int(citem_s)
            if ccode != pid:
                errors.append(f'checkbox {cid} not in phase {pid}')
            if f'{ccode}{cmnum}' != mid:
                errors.append(f'checkbox {cid} not under milestone {mid}')
            if cid in seen_checkbox:
                errors.append(f'duplicate checkbox id in {mid}: {cid}')
            seen_checkbox.add(cid)
            if prev_item is not None and citem < prev_item:
                errors.append(f'checkbox order regressed in {mid}: {citem} after {prev_item}')
            prev_item = citem
            if not ct:
                errors.append(f'missing checkbox title: {cid}')
            if status not in {'open', 'done'}:
                errors.append(f'invalid checkbox status for {cid}: {status}')

if errors:
    print('execution-ledger integrity check failed')
    for e in errors:
        print(f'- {e}')
    raise SystemExit(1)

print('execution-ledger integrity check passed')
PY
