#!/usr/bin/env python3
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

    seen_ids = set()
    seen_numbers = set()
    last = -1
    for ph in execution.get("phases", []):
      pid = ph.get("id")
      num = ph.get("number")
      if pid in seen_ids:
        errors.append(f"execution-ledger: duplicate phase id {pid}")
      if num in seen_numbers:
        errors.append(f"execution-ledger: duplicate phase number {num}")
      if isinstance(num, int):
        if num <= last:
          errors.append(f"execution-ledger: phase numbers not strictly increasing at {pid}")
        last = num
      seen_ids.add(pid)
      seen_numbers.add(num)

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
