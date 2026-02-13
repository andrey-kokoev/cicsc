#!/usr/bin/env python3
import re
import sys
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parents[2]


def load_yaml(rel: str):
    p = ROOT / rel
    if not p.exists():
        raise FileNotFoundError(rel)
    return yaml.safe_load(p.read_text(encoding="utf-8"))


def path_exists(rel: str) -> bool:
    return (ROOT / rel).exists()


def phase_prefix_to_num(mid: str, phase_id: str):
    if not mid.startswith(phase_id):
        return None
    suffix = mid[len(phase_id):]
    return int(suffix) if suffix.isdigit() else None


def main() -> int:
    errors = []

    objective = load_yaml("control-plane/objectives/objective-model.yaml")
    capability = load_yaml("control-plane/capabilities/capability-model.yaml")
    execution = load_yaml("control-plane/execution/execution-ledger.yaml")
    gate = load_yaml("control-plane/gates/gate-model.yaml")

    objective_ids = {o.get("id") for o in objective.get("objectives", [])}
    for cap in capability.get("capabilities", []):
        for ref in cap.get("objective_refs", []):
            if ref not in objective_ids:
                errors.append(f"capability-model: unknown objective ref {ref}")

    for o in objective.get("objectives", []):
        for signal in o.get("success_signals", []):
            ref = signal.get("ref")
            if isinstance(ref, str) and not path_exists(ref):
                errors.append(f"objective-model: missing referenced artifact {ref}")

    for cap in capability.get("capabilities", []):
        for check in cap.get("observable_checks", []):
            ref = check.get("ref")
            if isinstance(ref, str) and not path_exists(ref):
                errors.append(f"capability-model: missing referenced artifact {ref}")

    seen_phase_ids = set()
    seen_phase_numbers = set()
    last_phase_number = -1
    seen_checkbox_ids = set()

    milestone_re = re.compile(r"^[A-Z]{1,2}(\d+)$")

    for ph in execution.get("phases", []):
        pid = ph.get("id")
        pnum = ph.get("number")

        if pid in seen_phase_ids:
            errors.append(f"execution-ledger: duplicate phase id {pid}")
        if pnum in seen_phase_numbers:
            errors.append(f"execution-ledger: duplicate phase number {pnum}")
        if isinstance(pnum, int):
            if pnum <= last_phase_number:
                errors.append(f"execution-ledger: phase numbers not strictly increasing at {pid}")
            last_phase_number = pnum
        seen_phase_ids.add(pid)
        seen_phase_numbers.add(pnum)

        milestones = ph.get("milestones", [])
        last_mnum = -1
        seen_mids = set()

        for ms in milestones:
            mid = ms.get("id")
            if mid in seen_mids:
                errors.append(f"execution-ledger: duplicate milestone id within phase {pid}: {mid}")
            seen_mids.add(mid)

            m = milestone_re.match(mid or "")
            if not m:
                errors.append(f"execution-ledger: invalid milestone id format {mid}")
                continue
            mnum = phase_prefix_to_num(mid, pid)
            if mnum is None:
                errors.append(f"execution-ledger: milestone {mid} not prefixed by phase {pid}")
                continue
            if mnum <= last_mnum:
                errors.append(f"execution-ledger: milestone order not strictly increasing in {pid} at {mid}")
            last_mnum = mnum

            seen_cnums = set()
            for cb in ms.get("checkboxes", []):
                cid = cb.get("id")
                if cid in seen_checkbox_ids:
                    errors.append(f"execution-ledger: duplicate checkbox id {cid}")
                seen_checkbox_ids.add(cid)

                prefix = f"{mid}."
                if not isinstance(cid, str) or not cid.startswith(prefix):
                    errors.append(f"execution-ledger: checkbox {cid} not prefixed by milestone {mid}")
                    continue
                suffix = cid[len(prefix):]
                if not suffix.isdigit():
                    errors.append(f"execution-ledger: checkbox {cid} has non-numeric item suffix")
                    continue
                cnum = int(suffix)
                if cnum in seen_cnums:
                    errors.append(f"execution-ledger: duplicate checkbox item number in {mid}: {cid}")
                seen_cnums.add(cnum)

    for g in gate.get("gates", []):
        for script in g.get("required_scripts", []):
            if isinstance(script, str) and not path_exists(script):
                errors.append(f"gate-model: missing required script {script}")

    if errors:
        print("cross-model validation failed", file=sys.stderr)
        for e in errors:
            print(f"- {e}", file=sys.stderr)
        return 1

    print("cross-model validation passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
