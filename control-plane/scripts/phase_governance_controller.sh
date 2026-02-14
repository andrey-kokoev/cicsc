#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

LEDGER_FILE="${ROOT_DIR}/control-plane/execution/execution-ledger.yaml"
SCHEMA_FILE="${ROOT_DIR}/control-plane/execution/execution-ledger.schema.json"

# Modes
MODE_STATUS=0
MODE_PROMOTE=0
MODE_PROMOTE_NEXT=0
TARGET_PHASE=""
DRY_RUN=0
NO_COMMIT=0

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/phase_governance_controller.sh [options]

Commands:
  --status                 Show current phase governance status.
  --promote <PHASE_ID>     Promote a specific phase to active (e.g., AY).
  --promote-next           Promote the next planned phase to active.

Options:
  --dry-run                Validate preconditions without mutating ledger.
  --no-commit              Apply changes without committing.
  -h, --help               Show this message.

Phase Transition Rules:
  1. Only one phase may be 'active' at any time.
  2. A phase can only be promoted if the current active phase is 'complete'.
  3. A phase can only be promoted if its status is 'planned'.
  4. --promote-next selects the lowest-numbered planned phase.
  5. Promotion atomically sets current active to complete and target to active.

Examples:
  # Check current phase status
  ./control-plane/scripts/phase_governance_controller.sh --status

  # Promote specific phase
  ./control-plane/scripts/phase_governance_controller.sh --promote AY

  # Promote next planned phase (dry-run)
  ./control-plane/scripts/phase_governance_controller.sh --promote-next --dry-run

Exit Codes:
  0  Success
  1  Invalid arguments or validation failure
  2  Precondition check failure (phase not planned, active phase not complete, etc.)
USAGE
}

# Parse arguments
while [[ $# -gt 0 ]]; do
  case "$1" in
    --status) MODE_STATUS=1; shift ;;
    --promote) MODE_PROMOTE=1; TARGET_PHASE="${2:-}"; shift 2 ;;
    --promote-next) MODE_PROMOTE_NEXT=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    --no-commit) NO_COMMIT=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

# Validate command selection
mode_count=$((MODE_STATUS + MODE_PROMOTE + MODE_PROMOTE_NEXT))
if [[ "${mode_count}" -eq 0 ]]; then
  echo "error: no command specified (use --status, --promote, or --promote-next)" >&2
  usage >&2
  exit 1
fi
if [[ "${mode_count}" -gt 1 ]]; then
  echo "error: multiple commands specified (only one of --status, --promote, --promote-next allowed)" >&2
  exit 1
fi

cd "${ROOT_DIR}"

# Validate ledger exists and is valid YAML
if [[ ! -f "${LEDGER_FILE}" ]]; then
  echo "error: execution ledger not found: ${LEDGER_FILE}" >&2
  exit 1
fi

# Python helper for ledger operations
python_cmd() {
  python3 - "$@" <<'PY'
import sys
import yaml
from pathlib import Path

def load_ledger(path):
    return yaml.safe_load(Path(path).read_text(encoding="utf-8"))

def save_ledger(path, doc):
    Path(path).write_text(yaml.dump(doc, sort_keys=False, allow_unicode=True), encoding="utf-8")

def get_phase_statuses(doc):
    """Return dict of phase_id -> {number, status, title, index}"""
    phases = {}
    for idx, ph in enumerate(doc.get("phases", [])):
        phases[ph.get("id")] = {
            "number": ph.get("number"),
            "status": ph.get("status"),
            "title": ph.get("title"),
            "index": idx,
        }
    return phases

def get_active_phase(phases):
    """Return (phase_id, info) for the active phase, or None"""
    for pid, info in phases.items():
        if info.get("status") == "active":
            return (pid, info)
    return None

def get_planned_phases(phases):
    """Return list of (phase_id, info) sorted by phase number"""
    planned = [(pid, info) for pid, info in phases.items() if info.get("status") == "planned"]
    return sorted(planned, key=lambda x: x[1].get("number", 999))

def check_all_checkboxes_done(doc, phase_id):
    """Check if all checkboxes in a phase are done"""
    for ph in doc.get("phases", []):
        if ph.get("id") == phase_id:
            for ms in ph.get("milestones", []):
                for cb in ms.get("checkboxes", []):
                    if cb.get("status") != "done":
                        return False, cb.get("id")
            return True, None
    return False, "phase not found"

def format_status(doc, phases):
    """Format phase status for display"""
    lines = []
    lines.append("Phase Governance Status")
    lines.append("=" * 50)
    
    active = get_active_phase(phases)
    if active:
        pid, info = active
        lines.append(f"Active Phase:  {pid} (Phase {info['number']}) - {info['title']}")
    else:
        lines.append("Active Phase:  (none)")
    
    planned = get_planned_phases(phases)
    if planned:
        lines.append(f"Planned:       {len(planned)} phase(s)")
        for pid, info in planned[:3]:  # Show first 3
            lines.append(f"               - {pid} (Phase {info['number']}) - {info['title']}")
        if len(planned) > 3:
            lines.append(f"               ... and {len(planned) - 3} more")
    else:
        lines.append("Planned:       (none)")
    
    complete_count = sum(1 for info in phases.values() if info.get("status") == "complete")
    lines.append(f"Complete:      {complete_count} phase(s)")
    
    return "\n".join(lines)

def validate_promotion(doc, phases, target_id):
    """Validate promotion preconditions. Returns (ok, error_message)"""
    if target_id not in phases:
        return False, f"unknown phase: {target_id}"
    
    target = phases[target_id]
    if target.get("status") != "planned":
        return False, f"phase {target_id} is not 'planned' (status: {target.get('status')})"
    
    active = get_active_phase(phases)
    if active:
        active_id, active_info = active
        # Check if all checkboxes in active phase are done
        all_done, pending_cb = check_all_checkboxes_done(doc, active_id)
        if not all_done:
            return False, f"active phase {active_id} has incomplete checkbox: {pending_cb}"
    
    return True, ""

def do_promotion(doc, phases, target_id):
    """Perform promotion. Mutates doc. Returns (ok, error_message)"""
    ok, err = validate_promotion(doc, phases, target_id)
    if not ok:
        return False, err
    
    # Find and complete current active phase
    active = get_active_phase(phases)
    if active:
        active_id, _ = active
        for ph in doc.get("phases", []):
            if ph.get("id") == active_id:
                ph["status"] = "complete"
                break
    
    # Activate target phase
    for ph in doc.get("phases", []):
        if ph.get("id") == target_id:
            ph["status"] = "active"
            break
    
    return True, ""

# Main
command = sys.argv[1]
ledger_path = sys.argv[2]

doc = load_ledger(ledger_path)
phases = get_phase_statuses(doc)

if command == "status":
    print(format_status(doc, phases))
    sys.exit(0)

elif command == "validate-promote":
    target = sys.argv[3]
    ok, err = validate_promotion(doc, phases, target)
    if ok:
        print(f"validation passed: phase {target} can be promoted")
        sys.exit(0)
    else:
        print(f"validation failed: {err}")
        sys.exit(2)

elif command == "do-promote":
    target = sys.argv[3]
    ok, err = do_promotion(doc, phases, target)
    if not ok:
        print(f"promotion failed: {err}")
        sys.exit(2)
    save_ledger(ledger_path, doc)
    print(f"promoted phase {target} to active")
    # Show new status
    phases = get_phase_statuses(doc)
    print()
    print(format_status(doc, phases))
    sys.exit(0)

elif command == "get-next":
    planned = get_planned_phases(phases)
    if planned:
        print(planned[0][0])  # Print phase_id of next planned
        sys.exit(0)
    else:
        print("no planned phases available")
        sys.exit(2)

else:
    print(f"unknown command: {command}")
    sys.exit(1)
PY
}

# Validate ledger schema
validate_ledger() {
  if ! python3 -c "import yaml; yaml.safe_load(open('${LEDGER_FILE}'))" 2>/dev/null; then
    echo "error: execution ledger is not valid YAML" >&2
    exit 1
  fi
}

# Run ledger validation
cd "${ROOT_DIR}"
validate_ledger

# Execute command
if [[ "${MODE_STATUS}" -eq 1 ]]; then
  python_cmd status "${LEDGER_FILE}"
  exit 0
fi

if [[ "${MODE_PROMOTE}" -eq 1 ]]; then
  if [[ -z "${TARGET_PHASE}" ]]; then
    echo "error: --promote requires a PHASE_ID (e.g., AY)" >&2
    exit 1
  fi
  
  # Normalize phase ID (uppercase)
  TARGET_PHASE="${TARGET_PHASE^^}"
  
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "dry-run: validating promotion of phase ${TARGET_PHASE}..."
    python_cmd validate-promote "${LEDGER_FILE}" "${TARGET_PHASE}"
    exit $?
  fi
  
  # Validate first
  if ! python_cmd validate-promote "${LEDGER_FILE}" "${TARGET_PHASE}"; then
    exit 2
  fi
  
  # Apply promotion
  echo "promoting phase ${TARGET_PHASE} to active..."
  python_cmd do-promote "${LEDGER_FILE}" "${TARGET_PHASE}"
  
  # Regenerate views
  ./control-plane/scripts/generate_views.sh >/dev/null
  
  # Commit if not --no-commit
  if [[ "${NO_COMMIT}" -eq 0 ]]; then
    git add "${LEDGER_FILE}" control-plane/views/
    ./control-plane/scripts/collab_commit_views.sh --subject "governance/phase: promote ${TARGET_PHASE} to active" --no-refresh
  fi
  
  exit 0
fi

if [[ "${MODE_PROMOTE_NEXT}" -eq 1 ]]; then
  # Get next planned phase
  next_phase="$(python_cmd get-next "${LEDGER_FILE}" 2>/dev/null)" || {
    echo "error: no planned phases available for promotion" >&2
    exit 2
  }
  
  echo "next planned phase: ${next_phase}"
  
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "dry-run: validating promotion..."
    python_cmd validate-promote "${LEDGER_FILE}" "${next_phase}"
    exit $?
  fi
  
  # Validate first
  if ! python_cmd validate-promote "${LEDGER_FILE}" "${next_phase}"; then
    exit 2
  fi
  
  # Apply promotion
  echo "promoting phase ${next_phase} to active..."
  python_cmd do-promote "${LEDGER_FILE}" "${next_phase}"
  
  # Regenerate views
  ./control-plane/scripts/generate_views.sh >/dev/null
  
  # Commit if not --no-commit
  if [[ "${NO_COMMIT}" -eq 0 ]]; then
    git add "${LEDGER_FILE}" control-plane/views/
    ./control-plane/scripts/collab_commit_views.sh --subject "governance/phase: promote ${next_phase} to active (auto-next)" --no-refresh
  fi
  
  exit 0
fi

echo "error: unknown command state" >&2
exit 1
