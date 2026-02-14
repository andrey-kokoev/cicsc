#!/usr/bin/env bash
set -uo pipefail

on_err() {
  local rc="$?"
  local cmd="${BASH_COMMAND:-unknown}"
  echo "autopilot fatal: rc=${rc} cmd=${cmd}" >&2
}
trap on_err ERR

on_exit() {
  local rc="$?"
  if [[ "${rc}" -eq 0 ]]; then
    echo "autopilot exit: rc=0" >&2
  else
    echo "autopilot exit: rc=${rc}" >&2
  fi
}
trap on_exit EXIT

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

AGENT_REF="AGENT_KIMI"
BATCH_SIZE=3
MAX_CYCLES=0
MAX_INFLIGHT=0
INTERVAL_SECONDS=5
WAIT_TIMEOUT_SECONDS=0
FRICTION_DECISION="accept_later"
FRICTION_BACKLOG_REF=""
FRICTION_NOTES=""
QUIET=0
DRY_RUN=0
CONTINUE_ON_ERROR=1
ERROR_SLEEP_SECONDS=5

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_autopilot.sh [options]

Options:
  --agent-ref <AGENT_...>      Target worker agent (default: AGENT_KIMI).
  --batch-size <n>             Dispatch batch size (default: 3).
  --max-cycles <n>             Max dispatch cycles (0 = infinite, default: 0).
  --max-inflight <n>           Max worker pending before new dispatch (default: 0).
  --interval-seconds <n>       Poll interval for wait loops (default: 5).
  --wait-timeout-seconds <n>   Per-cycle wait timeout for ingestable work (0 = no timeout).
  --friction-decision <accept_now|accept_later|reject>
                               Main friction triage decision (default: accept_later).
  --friction-backlog-ref <id>  Optional backlog ref for accept_later.
  --friction-notes <text>      Optional triage note.
  --dry-run                    Print planned actions without mutating.
  --quiet                      Reduce log output.
  --fail-fast                  Exit on first process/dispatch failure.
  --error-sleep-seconds <n>    Backoff after recoverable errors (default: 5).

Semantics:
  Loop: process main ingestables -> wait until worker pending <= max_inflight -> dispatch batch
  -> wait for new ingestables -> process main -> repeat.
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --agent-ref) AGENT_REF="${2:-}"; shift 2 ;;
    --batch-size) BATCH_SIZE="${2:-}"; shift 2 ;;
    --max-cycles) MAX_CYCLES="${2:-}"; shift 2 ;;
    --max-inflight) MAX_INFLIGHT="${2:-}"; shift 2 ;;
    --interval-seconds) INTERVAL_SECONDS="${2:-}"; shift 2 ;;
    --wait-timeout-seconds) WAIT_TIMEOUT_SECONDS="${2:-}"; shift 2 ;;
    --friction-decision) FRICTION_DECISION="${2:-}"; shift 2 ;;
    --friction-backlog-ref) FRICTION_BACKLOG_REF="${2:-}"; shift 2 ;;
    --friction-notes) FRICTION_NOTES="${2:-}"; shift 2 ;;
    --dry-run) DRY_RUN=1; shift ;;
    --quiet) QUIET=1; shift ;;
    --fail-fast) CONTINUE_ON_ERROR=0; shift ;;
    --error-sleep-seconds) ERROR_SLEEP_SECONDS="${2:-}"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

for pair in \
  "BATCH_SIZE:$BATCH_SIZE" \
  "MAX_CYCLES:$MAX_CYCLES" \
  "MAX_INFLIGHT:$MAX_INFLIGHT" \
  "INTERVAL_SECONDS:$INTERVAL_SECONDS" \
  "WAIT_TIMEOUT_SECONDS:$WAIT_TIMEOUT_SECONDS" \
  "ERROR_SLEEP_SECONDS:$ERROR_SLEEP_SECONDS"; do
  name="${pair%%:*}"; val="${pair##*:}"
  if ! [[ "${val}" =~ ^[0-9]+$ ]]; then
    echo "${name} must be an integer >= 0" >&2
    exit 1
  fi
  if [[ "${name}" == "BATCH_SIZE" || "${name}" == "INTERVAL_SECONDS" ]] && [[ "${val}" -lt 1 ]]; then
    echo "${name} must be >= 1" >&2
    exit 1
  fi
done
if [[ "${FRICTION_DECISION}" != "accept_now" && "${FRICTION_DECISION}" != "accept_later" && "${FRICTION_DECISION}" != "reject" ]]; then
  echo "--friction-decision must be accept_now, accept_later, or reject" >&2
  exit 1
fi

cd "${ROOT_DIR}"

if [[ "${QUIET}" -eq 0 ]]; then
  echo "autopilot start: agent=${AGENT_REF} batch=${BATCH_SIZE} max_cycles=${MAX_CYCLES} max_inflight=${MAX_INFLIGHT} interval=${INTERVAL_SECONDS}s timeout=${WAIT_TIMEOUT_SECONDS}s"
fi

counts_for_agent() {
  python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$AGENT_REF" <<'PY'
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
agent_ref = sys.argv[2]
messages = [m for m in collab.get("messages", []) if m.get("to_agent_ref") == agent_ref]
by_mid = {}
for e in collab.get("message_events", []):
    by_mid.setdefault(e.get("message_ref"), []).append(e)

pending = 0
ingestable = 0
for m in messages:
    evs = sorted(by_mid.get(m.get("id"), []), key=lambda e: int(e.get("at_seq", 0)))
    cur = evs[-1].get("to_status") if evs else m.get("initial_status")
    if cur in {"queued", "sent", "acknowledged"}:
        pending += 1
    if cur in {"fulfilled", "ingested"}:
        ingestable += 1
print(pending)
print(ingestable)
PY
}

read_counts_safe() {
  local attempts=0
  local max_attempts=3
  while (( attempts < max_attempts )); do
    if readarray -t c < <(counts_for_agent); then
      pending="${c[0]:-0}"
      ingestable="${c[1]:-0}"
      return 0
    fi
    attempts=$((attempts + 1))
    echo "autopilot warning: counts_for_agent failed (attempt ${attempts}/${max_attempts})" >&2
    sleep 1
  done
  return 1
}

run_main_process() {
  cmd=(
    ./control-plane/scripts/collab_process_messages.sh
    --role main
    --agent-ref "${AGENT_REF}"
    --with-friction-triage
    --friction-decision "${FRICTION_DECISION}"
  )
  [[ -n "${FRICTION_BACKLOG_REF}" ]] && cmd+=(--friction-backlog-ref "${FRICTION_BACKLOG_REF}")
  [[ -n "${FRICTION_NOTES}" ]] && cmd+=(--friction-notes "${FRICTION_NOTES}")

  if [[ "${DRY_RUN}" -eq 1 ]]; then
    echo "dry-run: ${cmd[*]}"
  else
    "${cmd[@]}"
  fi
}

run_dispatch() {
  cmd=(
    ./control-plane/scripts/collab_dispatch_batch.sh
    --agent-ref "${AGENT_REF}"
    --count "${BATCH_SIZE}"
    --subject "governance/collab: autopilot dispatch to ${AGENT_REF}"
    --body "Autopilot batch dispatch to ${AGENT_REF}."
  )
  if [[ "${DRY_RUN}" -eq 1 ]]; then
    cmd+=(--dry-run)
    echo "dry-run: ${cmd[*]}"
  else
    "${cmd[@]}"
  fi
}

safe_step() {
  local label="$1"
  shift
  local rc=0
  "$@"
  rc=$?
  if [[ "${rc}" -eq 0 ]]; then
    return 0
  fi
  echo "autopilot error: ${label} failed (exit=${rc})" >&2
  if [[ "${CONTINUE_ON_ERROR}" -eq 0 ]]; then
    exit "${rc}"
  fi
  echo "autopilot recoverable path: sleeping ${ERROR_SLEEP_SECONDS}s before retry loop" >&2
  sleep "${ERROR_SLEEP_SECONDS}"
  return "${rc}"
}

cycle=0
while true; do
  if [[ "${MAX_CYCLES}" -gt 0 && "${cycle}" -ge "${MAX_CYCLES}" ]]; then
    if [[ "${QUIET}" -eq 0 ]]; then
      echo "autopilot complete: reached max cycles ${MAX_CYCLES}"
    fi
    break
  fi

  # Drain ingestable work first.
  if [[ "${QUIET}" -eq 0 ]]; then
    echo "[cycle ${cycle}] process main"
  fi
  safe_step "process-main@cycle-${cycle}" run_main_process || continue

  # Wait until worker backlog is below threshold.
  while true; do
    if ! read_counts_safe; then
      echo "autopilot error: unable to read counts; deferring cycle" >&2
      sleep "${ERROR_SLEEP_SECONDS}"
      continue
    fi
    if [[ "${pending}" -le "${MAX_INFLIGHT}" ]]; then
      break
    fi
    if [[ "${QUIET}" -eq 0 ]]; then
      echo "[cycle ${cycle}] pending=${pending} (> ${MAX_INFLIGHT}), waiting ${INTERVAL_SECONDS}s"
    fi
    sleep "${INTERVAL_SECONDS}"
    safe_step "process-main-backlog@cycle-${cycle}" run_main_process || continue
  done

  if [[ "${QUIET}" -eq 0 ]]; then
    echo "[cycle ${cycle}] dispatch batch size ${BATCH_SIZE}"
  fi
  safe_step "dispatch@cycle-${cycle}" run_dispatch || continue
  cycle=$((cycle + 1))

  # Wait for ingestable work from worker before next dispatch cycle.
  started="$(date +%s)"
  while true; do
    if ! read_counts_safe; then
      echo "autopilot warning: unable to read counts while waiting; retrying" >&2
      sleep "${INTERVAL_SECONDS}"
      continue
    fi
    if [[ "${ingestable}" -gt 0 ]]; then
      if [[ "${QUIET}" -eq 0 ]]; then
        echo "[cycle ${cycle}] ingestable=${ingestable}; running main process"
      fi
      safe_step "process-main-ingestable@cycle-${cycle}" run_main_process || true
      break
    fi

    if [[ "${WAIT_TIMEOUT_SECONDS}" -gt 0 ]]; then
      now="$(date +%s)"
      elapsed=$((now - started))
      if [[ "${elapsed}" -ge "${WAIT_TIMEOUT_SECONDS}" ]]; then
        if [[ "${QUIET}" -eq 0 ]]; then
          echo "[cycle ${cycle}] wait timeout (${elapsed}s) without ingestable work"
        fi
        break
      fi
    fi

    if [[ "${QUIET}" -eq 0 ]]; then
      echo "[cycle ${cycle}] waiting for worker progress; pending=${pending}, ingestable=${ingestable}"
    fi
    sleep "${INTERVAL_SECONDS}"
  done

done
