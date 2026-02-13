#!/usr/bin/env python3
import json
import sys
from pathlib import Path

import yaml


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: export_execution_status.py <execution-ledger.yaml>", file=sys.stderr)
        return 2

    source = Path(sys.argv[1])
    if not source.exists():
        print(f"missing execution ledger: {source}", file=sys.stderr)
        return 2

    ledger = yaml.safe_load(source.read_text(encoding="utf-8"))
    rows = []
    for phase in ledger.get("phases", []):
        phase_id = phase.get("id")
        phase_no = phase.get("number")
        for milestone in phase.get("milestones", []):
            for checkbox in milestone.get("checkboxes", []):
                rows.append(
                    {
                        "phase_id": phase_id,
                        "phase_number": phase_no,
                        "checkbox_id": checkbox.get("id"),
                        "status": checkbox.get("status"),
                    }
                )

    payload = {
        "_generated": True,
        "_source": str(source),
        "_generator": "control-plane/scripts/export_execution_status.py",
        "version": "cicsc/execution-status-v1",
        "status_source_mode": ledger.get("status_source_mode"),
        "rows": rows,
    }
    json.dump(payload, sys.stdout, indent=2)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
