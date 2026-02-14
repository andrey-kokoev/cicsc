#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"
MESSAGE_REF=""
WORKTREE="${PWD}"
ACTOR_AGENT=""
COMMIT_SHA=""
NOTES=""
NO_REFRESH=0
DRY_RUN=0
SUGGEST_COMMIT=0
AUTO_COMMIT=0
COMMIT_SUBJECT=""
COMMIT_BODY=()
LAZY=0
MAX_AGE_MINUTES=30
RUN_SCRIPTS=()
DEPS=()
WITH_ITEMS=()
AUTO_REPORT=0
QUIET=0
SUMMARY=0
SCRIPT_REFS=()
GATE_REFS=()
THEOREM_REFS=()
DIFFLOG_REFS=()
RAW_EVIDENCE=()

usage() {
  cat <<'USAGE'
Usage:
  control-plane/scripts/collab_fulfill.sh --message-ref MSG_... [options]

Options:
  --worktree <path>     Worktree path key (default: current $PWD).
  --actor-agent-ref <id>
                        Explicit actor override (default: owner agent of worktree).
  --commit <sha>        Commit to bind on event (default: current HEAD short).
  --notes <text>        Optional event note.
  --script <path>       Add evidence binding with kind EVID_SCRIPT.
  --gate-report <path>  Add evidence binding with kind EVID_GATE_REPORT.
  --theorem <path>      Add evidence binding with kind EVID_THEOREM.
  --diff-log <path>     Add evidence binding with kind EVID_DIFFERENTIAL_LOG.
  --evidence <ref|EVID_KIND>
                        Add custom typed evidence (digest auto-computed from ref path).
  --no-refresh          Do not regenerate mailbox projection after append.
  --dry-run             Validate and resolve evidence bindings, but do not append event.
  --suggest-commit      Print a suggested git commit command after fulfill.
  --auto-commit         Auto-commit collab model/views after fulfill (requires clean tree).
  --commit-subject <t>  Commit subject override when --auto-commit is set.
  --message <t>         Alias for --commit-subject.
  --commit-body <t>     Additional commit body line (repeatable) for --auto-commit.
  --run-script <cmd>    Execute a script/command before fulfill (repeatable).
  --with <path|cmd>     Sugar: add script evidence + execute command in one flag.
  --auto-report         Auto-select gate report from script header/recent docs artifacts.
  --report-auto         Alias for --auto-report.
  --dep <path>          Additional dependency path for --lazy freshness checks (repeatable).
  --lazy                Skip --run-script when evidence appears fresh.
  --max-age-minutes <n> Freshness TTL for --lazy (default: 30).
  --quiet               Minimize output noise.
  --summary             Print concise fulfillment summary (implies --quiet).
USAGE
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --message-ref) MESSAGE_REF="${2:-}"; shift 2 ;;
    --worktree) WORKTREE="${2:-}"; shift 2 ;;
    --actor-agent-ref) ACTOR_AGENT="${2:-}"; shift 2 ;;
    --commit) COMMIT_SHA="${2:-}"; shift 2 ;;
    --notes) NOTES="${2:-}"; shift 2 ;;
    --script) SCRIPT_REFS+=("${2:-}"); shift 2 ;;
    --gate-report) GATE_REFS+=("${2:-}"); shift 2 ;;
    --theorem) THEOREM_REFS+=("${2:-}"); shift 2 ;;
    --diff-log) DIFFLOG_REFS+=("${2:-}"); shift 2 ;;
    --evidence) RAW_EVIDENCE+=("${2:-}"); shift 2 ;;
    --no-refresh) NO_REFRESH=1; shift ;;
    --dry-run) DRY_RUN=1; shift ;;
    --suggest-commit) SUGGEST_COMMIT=1; shift ;;
    --auto-commit) AUTO_COMMIT=1; shift ;;
    --commit-subject) COMMIT_SUBJECT="${2:-}"; shift 2 ;;
    --message) COMMIT_SUBJECT="${2:-}"; shift 2 ;;
    --commit-body) COMMIT_BODY+=("${2:-}"); shift 2 ;;
    --run-script) RUN_SCRIPTS+=("${2:-}"); shift 2 ;;
    --with) WITH_ITEMS+=("${2:-}"); shift 2 ;;
    --auto-report|--report-auto) AUTO_REPORT=1; shift ;;
    --dep) DEPS+=("${2:-}"); shift 2 ;;
    --lazy) LAZY=1; shift ;;
    --max-age-minutes) MAX_AGE_MINUTES="${2:-}"; shift 2 ;;
    --quiet) QUIET=1; shift ;;
    --summary) SUMMARY=1; QUIET=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "unknown option: $1" >&2; usage >&2; exit 1 ;;
  esac
done

if [[ -z "${MESSAGE_REF}" ]]; then
  echo "--message-ref is required" >&2
  usage >&2
  exit 1
fi
if ! [[ "${MAX_AGE_MINUTES}" =~ ^[0-9]+$ ]] || [[ "${MAX_AGE_MINUTES}" -lt 1 ]]; then
  echo "--max-age-minutes must be a positive integer" >&2
  exit 1
fi

cd "${ROOT_DIR}"

# Auto-sync before operation to ensure fresh state
if [[ "${DRY_RUN}" -eq 0 ]]; then
  ./control-plane/scripts/generate_views.sh >/dev/null 2>&1 || true
fi

# Check dirty state - fail with helpful message
if [[ "${AUTO_COMMIT}" -eq 1 && "${DRY_RUN}" -eq 0 ]]; then
  _dirty_non_collab="$(git status --porcelain -- . ':(exclude)control-plane/collaboration/collab-model.yaml' ':(exclude)control-plane/views' ':(exclude)control-plane/logs' || true)"
  if [[ -n "${_dirty_non_collab}" ]]; then
    echo "ERROR: cannot auto-commit: working tree has uncommitted changes" >&2
    echo "" >&2
    echo "Dirty files (excluding collab model/views):" >&2
    echo "${_dirty_non_collab}" | head -10 >&2
    echo "" >&2
    echo "Recovery options:" >&2
    echo "  1. Commit changes: git add -A && git commit -m 'your message'" >&2
    echo "  2. Stash changes: git stash" >&2
    echo "  3. Run without --auto-commit (commit manually after)" >&2
    exit 1
  fi
fi

# Validate but don't fail on cross-model issues (will be caught by specific checks)
./control-plane/scripts/collab_validate.sh >/dev/null 2>&1 || true

if [[ -z "${COMMIT_SHA}" ]]; then
  COMMIT_SHA="$(git rev-parse --short HEAD)"
fi

if [[ -z "${ACTOR_AGENT}" ]]; then
  ACTOR_AGENT="$(
    python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$WORKTREE" <<'PY'
import sys
from pathlib import Path
import yaml
collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
worktree = sys.argv[2]
agent = next((a for a in collab.get("agents", []) if a.get("worktree") == worktree), None)
if agent is None:
    raise SystemExit(f"no agent mapped to worktree {worktree}")
print(agent.get("id"))
PY
  )"
fi

# Verify message is in 'acknowledged' state
_msg_status="$(
  python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$MESSAGE_REF" <<'PY'
import sys
from pathlib import Path
import yaml
collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
msg_ref = sys.argv[2]
events = sorted([e for e in collab.get("message_events", []) if e.get("message_ref") == msg_ref], key=lambda x: int(x.get("at_seq", 0)))
if events:
    print(events[-1].get("to_status"))
else:
    msg = next((m for m in collab.get("messages", []) if m.get("id") == msg_ref), None)
    print(msg.get("initial_status", "sent") if msg else "unknown")
PY
)"

if [[ "${_msg_status}" != "acknowledged" ]]; then
  echo "error: message ${MESSAGE_REF} is in status '${_msg_status}'" >&2
  echo "hint: message must be 'acknowledged' before fulfillment" >&2
  echo "hint: run ./control-plane/scripts/collab_claim_next.sh first" >&2
  exit 1
fi

if [[ -z "${NOTES}" ]]; then
  NOTES="Fulfilled by ${ACTOR_AGENT} via collab_fulfill.sh"
fi

to_abs_path() {
  python3 - "$ROOT_DIR" "$1" <<'PY'
import os, sys
root = os.path.abspath(sys.argv[1])
path = sys.argv[2]
ap = os.path.abspath(path if os.path.isabs(path) else os.path.join(root, path))
if not ap.startswith(root + os.sep):
    raise SystemExit(f"path outside repo: {path}")
print(ap)
PY
}

to_rel_path() {
  python3 - "$ROOT_DIR" "$1" <<'PY'
import os, sys
root = os.path.abspath(sys.argv[1])
path = sys.argv[2]
ap = os.path.abspath(path if os.path.isabs(path) else os.path.join(root, path))
if not ap.startswith(root + os.sep):
    raise SystemExit(f"path outside repo: {path}")
print(os.path.relpath(ap, root))
PY
}

extract_header_single() {
  local file="$1"
  local key="$2"
  grep -E "^[[:space:]]*#[[:space:]]*${key}:[[:space:]]*" "${file}" | head -n 1 | sed -E "s/^[[:space:]]*#[[:space:]]*${key}:[[:space:]]*//"
}

append_unique() {
  local value="$1"
  shift
  local -n arr_ref="$1"
  for existing in "${arr_ref[@]}"; do
    [[ "${existing}" == "${value}" ]] && return 0
  done
  arr_ref+=("${value}")
}

mk_evidence_item() {
  local ref="$1"
  local kind="$2"
  local rel
  rel="$(to_rel_path "${ref}")"
  if [[ ! -f "${ROOT_DIR}/${rel}" ]]; then
    echo "missing evidence file: ${rel}" >&2
    exit 1
  fi
  local digest
  digest="$(sha256sum "${ROOT_DIR}/${rel}" | awk '{print $1}')"
  echo "${rel}|${kind}|${COMMIT_SHA}|sha256:${digest}"
}

if [[ ${#WITH_ITEMS[@]} -gt 0 ]]; then
  for w in "${WITH_ITEMS[@]}"; do
    if abs="$(to_abs_path "${w}" 2>/dev/null)" && [[ -f "${abs}" ]]; then
      append_unique "${w}" SCRIPT_REFS
      append_unique "${w}" RUN_SCRIPTS
    else
      append_unique "${w}" RUN_SCRIPTS
    fi
  done
fi

# Derive default deps/report hints from script headers.
for s in "${SCRIPT_REFS[@]}"; do
  if abs="$(to_abs_path "${s}" 2>/dev/null)" && [[ -f "${abs}" ]]; then
    rep="$(extract_header_single "${abs}" "collab-report" || true)"
    if [[ -n "${rep}" && "${AUTO_REPORT}" -eq 1 && ${#GATE_REFS[@]} -eq 0 ]]; then
      append_unique "${rep}" GATE_REFS
    fi
    dep_line="$(extract_header_single "${abs}" "collab-deps" || true)"
    if [[ -n "${dep_line}" ]]; then
      IFS=',' read -r -a _deps <<<"${dep_line}"
      for d in "${_deps[@]}"; do
        d="$(echo "${d}" | xargs)"
        [[ -n "${d}" ]] && append_unique "${d}" DEPS
      done
    fi
  fi
done

if [[ ${#RUN_SCRIPTS[@]} -gt 0 ]]; then
  _run_start_epoch="$(date +%s)"
  _checks_passed=0
  _checks_failed=0
  _target_report=""
  if [[ ${#GATE_REFS[@]} -gt 0 ]]; then
    _target_report="$(to_abs_path "${GATE_REFS[0]}")"
  fi
  for cmdline in "${RUN_SCRIPTS[@]}"; do
    should_run=1
    reason="no-lazy"
    if [[ "${LAZY}" -eq 1 ]]; then
      should_run=0
      reason="fresh-skip"
      if [[ -z "${_target_report}" || ! -f "${_target_report}" ]]; then
        should_run=1
        reason="missing-report"
      else
        report_mtime="$(stat -c %Y "${_target_report}")"
        now_epoch="$(date +%s)"
        age_secs=$((now_epoch - report_mtime))
        if [[ "${age_secs}" -gt $((MAX_AGE_MINUTES * 60)) ]]; then
          should_run=1
          reason="report-too-old"
        else
          newest_dep=0
          # always include core protocol models as lazy deps
          for base_dep in control-plane/collaboration/collab-model.yaml control-plane/execution/execution-ledger.yaml; do
            ap="$(to_abs_path "${base_dep}")"
            [[ -e "${ap}" ]] || continue
            mt="$(stat -c %Y "${ap}")"
            if [[ "${mt}" -gt "${newest_dep}" ]]; then newest_dep="${mt}"; fi
          done
          for ref in "${SCRIPT_REFS[@]}"; do
            ap="$(to_abs_path "${ref}")"
            [[ -f "${ap}" ]] || continue
            mt="$(stat -c %Y "${ap}")"
            if [[ "${mt}" -gt "${newest_dep}" ]]; then newest_dep="${mt}"; fi
          done
          for ref in "${DEPS[@]}"; do
            ap="$(to_abs_path "${ref}")"
            [[ -e "${ap}" ]] || continue
            mt="$(stat -c %Y "${ap}")"
            if [[ "${mt}" -gt "${newest_dep}" ]]; then newest_dep="${mt}"; fi
          done
          if [[ "${newest_dep}" -gt "${report_mtime}" ]]; then
            should_run=1
            reason="deps-newer-than-report"
          fi
        fi
      fi
    fi
    if [[ "${should_run}" -eq 1 ]]; then
      [[ "${QUIET}" -eq 0 ]] && echo "run-script: executing (${reason}): ${cmdline}"
      if [[ "${QUIET}" -eq 1 ]]; then
        if bash -lc "${cmdline}" >/dev/null 2>&1; then
          _checks_passed=$((_checks_passed + 1))
        else
          _checks_failed=$((_checks_failed + 1))
          echo "run-script failed: ${cmdline}" >&2
          exit 1
        fi
      else
        bash -lc "${cmdline}"
        _checks_passed=$((_checks_passed + 1))
      fi
    else
      [[ "${QUIET}" -eq 0 ]] && echo "run-script: skipping (${reason}): ${cmdline}"
    fi
  done
fi

if [[ "${AUTO_REPORT}" -eq 1 && ${#GATE_REFS[@]} -eq 0 ]]; then
  _auto_report=""
  # Prefer freshly updated report since run start.
  _auto_report="$(find docs/pilot -maxdepth 1 -name '*.json' -type f -printf '%T@ %p\n' 2>/dev/null | sort -nr | awk -v s="${_run_start_epoch:-0}" '$1 >= (s-1) {print $2; exit}')"
  if [[ -z "${_auto_report}" && ${#SCRIPT_REFS[@]} -gt 0 ]]; then
    _stem="$(basename "${SCRIPT_REFS[0]}")"
    _stem="${_stem%.*}"
    _stem="${_stem#check_}"
    _auto_report="$(find docs/pilot -maxdepth 1 -name "*${_stem}*.json" -type f -printf '%T@ %p\n' 2>/dev/null | sort -nr | awk 'NR==1 {print $2}')"
  fi
  if [[ -z "${_auto_report}" ]]; then
    _auto_report="$(find docs/pilot -maxdepth 1 -name '*.json' -type f -printf '%T@ %p\n' 2>/dev/null | sort -nr | awk 'NR==1 {print $2}')"
  fi
  if [[ -n "${_auto_report}" ]]; then
    append_unique "${_auto_report}" GATE_REFS
    [[ "${QUIET}" -eq 0 ]] && echo "auto-report: selected ${_auto_report}"
  else
    echo "auto-report: no candidate report found under docs/pilot" >&2
    exit 1
  fi
fi

EVIDENCE_ITEMS=()
for ref in "${SCRIPT_REFS[@]}"; do
  EVIDENCE_ITEMS+=("$(mk_evidence_item "${ref}" "EVID_SCRIPT")")
done
for ref in "${GATE_REFS[@]}"; do
  EVIDENCE_ITEMS+=("$(mk_evidence_item "${ref}" "EVID_GATE_REPORT")")
done
for ref in "${THEOREM_REFS[@]}"; do
  EVIDENCE_ITEMS+=("$(mk_evidence_item "${ref}" "EVID_THEOREM")")
done
for ref in "${DIFFLOG_REFS[@]}"; do
  EVIDENCE_ITEMS+=("$(mk_evidence_item "${ref}" "EVID_DIFFERENTIAL_LOG")")
done
for item in "${RAW_EVIDENCE[@]}"; do
  kind="${item##*|}"
  ref="${item%|*}"
  EVIDENCE_ITEMS+=("$(mk_evidence_item "${ref}" "${kind}")")
done

if [[ ${#EVIDENCE_ITEMS[@]} -eq 0 ]]; then
  echo "at least one evidence binding is required for fulfill" >&2
  exit 1
fi

cmd=(
  ./control-plane/scripts/collab_append_event.sh
  --message-ref "${MESSAGE_REF}"
  --to-status fulfilled
  --actor-agent-ref "${ACTOR_AGENT}"
  --commit "${COMMIT_SHA}"
  --notes "${NOTES}"
)
if [[ "${NO_REFRESH}" -eq 1 ]]; then
  cmd+=(--no-refresh)
fi
if [[ "${DRY_RUN}" -eq 1 ]]; then
  cmd+=(--dry-run)
fi
for e in "${EVIDENCE_ITEMS[@]}"; do
  cmd+=(--evidence "${e}")
done

if [[ "${QUIET}" -eq 1 ]]; then
  "${cmd[@]}" >/dev/null
else
  "${cmd[@]}"
fi
if [[ "${DRY_RUN}" -eq 1 ]]; then
  echo "dry-run: would fulfill message ${MESSAGE_REF}"
else
  ./control-plane/scripts/collab_validate.sh >/dev/null
  _summary="$(
    python3 - "$ROOT_DIR/control-plane/collaboration/collab-model.yaml" "$MESSAGE_REF" "$WORKTREE" <<'PY'
import sys
from pathlib import Path
import yaml

collab = yaml.safe_load(Path(sys.argv[1]).read_text(encoding="utf-8"))
message_ref = sys.argv[2]
worktree = sys.argv[3]
messages = collab.get("messages", [])
events = collab.get("message_events", [])

msg = next((m for m in messages if m.get("id") == message_ref), None)
if msg is None:
    raise SystemExit("unknown message")
assignment_ref = msg.get("assignment_ref")
assignments = {a.get("id"): a for a in collab.get("assignments", [])}
checkbox_ref = (assignments.get(assignment_ref) or {}).get("checkbox_ref", "")

events_by_message = {}
for e in events:
    events_by_message.setdefault(e.get("message_ref"), []).append(e)

remaining = 0
for m in messages:
    if m.get("to_worktree") != worktree:
        continue
    evs = sorted(events_by_message.get(m.get("id"), []), key=lambda e: int(e.get("at_seq", 0)))
    cur = evs[-1].get("to_status") if evs else m.get("initial_status")
    if cur in {"queued", "sent"}:
        remaining += 1

print(assignment_ref)
print(checkbox_ref)
print(remaining)
PY
  )"
  readarray -t _sum_lines <<<"${_summary}"
  _assignment_ref="${_sum_lines[0]}"
  _checkbox_ref="${_sum_lines[1]}"
  _remaining="${_sum_lines[2]}"
  if [[ "${SUMMARY}" -eq 1 ]]; then
    echo "fulfilled: ${MESSAGE_REF}"
    echo "assignment: ${_assignment_ref}"
    echo "checks: ${_checks_passed:-0} passed, ${_checks_failed:-0} failed"
    echo "next: ${_remaining} actionable"
  else
    echo "fulfilled message: ${MESSAGE_REF}"
    echo "assignment: ${_assignment_ref}"
    echo "remaining actionable in ${WORKTREE}: ${_remaining}"
  fi
  if [[ "${SUGGEST_COMMIT}" -eq 1 ]]; then
    _subject="governance/collab: fulfill ${_assignment_ref}"
    if [[ -n "${_checkbox_ref}" ]]; then
      _subject="governance/collab: fulfill ${_checkbox_ref} (${_assignment_ref})"
    fi
    echo "suggested commit:"
    echo "git add control-plane/collaboration/collab-model.yaml control-plane/views/ && \\"
    echo "  git commit -m \"${_subject}\""
  fi
  if [[ "${AUTO_COMMIT}" -eq 1 ]]; then
    _commit_cmd=(./control-plane/scripts/collab_commit_views.sh --from-last-collab-action)
    if [[ -n "${COMMIT_SUBJECT}" ]]; then
      _commit_cmd+=(--subject "${COMMIT_SUBJECT}")
    fi
    for line in "${COMMIT_BODY[@]}"; do
      _commit_cmd+=(--body "${line}")
    done
    "${_commit_cmd[@]}"
    if [[ "${SUMMARY}" -eq 1 ]]; then
      echo "committed: $(git rev-parse --short HEAD)"
    else
      echo "auto-committed collab model/views"
    fi
  fi
fi
