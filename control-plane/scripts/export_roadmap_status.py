#!/usr/bin/env python3
import json
import re
import sys
from pathlib import Path

PHASE_RE = re.compile(r"^## ([A-Z]{1,2})\. Phase (\d+):\s+(.+)$")
CHECKBOX_RE = re.compile(r"^- \[(x| )\] ([A-Z]{1,2}\d+\.\d+)\s+(.+)$")


def parse(lines):
    phase_id = None
    phase_number = None
    rows = []

    for line in lines:
        pm = PHASE_RE.match(line)
        if pm:
            phase_id = pm.group(1)
            phase_number = int(pm.group(2))
            continue

        cm = CHECKBOX_RE.match(line)
        if cm and phase_id is not None:
            rows.append(
                {
                    "phase_id": phase_id,
                    "phase_number": phase_number,
                    "checkbox_id": cm.group(2),
                    "title": cm.group(3).strip(),
                    "status": "done" if cm.group(1) == "x" else "open",
                }
            )

    return rows


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: export_roadmap_status.py <ROADMAP.md>", file=sys.stderr)
        return 2

    source = Path(sys.argv[1])
    if not source.exists():
        print(f"missing roadmap file: {source}", file=sys.stderr)
        return 1

    rows = parse(source.read_text(encoding="utf-8").splitlines())
    out = {
        "_generated": True,
        "_source": str(source),
        "_generator": "control-plane/scripts/export_roadmap_status.py",
        "version": "cicsc/roadmap-status-v1",
        "rows": rows,
    }
    print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
