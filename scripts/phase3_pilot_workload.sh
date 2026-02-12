#!/usr/bin/env bash
set -euo pipefail

SERVER_URL="${SERVER_URL:-http://localhost}"
TENANT_ID="${TENANT_ID:-pilot_t1}"
DRY_RUN="${DRY_RUN:-1}"

run() {
  if [[ "${DRY_RUN}" == "1" ]]; then
    echo "DRY_RUN $*"
  else
    eval "$@"
  fi
}

# 1) Compile and install (if needed)
run "curl -sS -X POST '${SERVER_URL}/compile' -H 'content-type: application/json' -d @verticals/ticketing/spec.v1.json"
run "curl -sS -X POST '${SERVER_URL}/install-from-spec?tenant_id=${TENANT_ID}' -H 'content-type: application/json' -d @verticals/ticketing/spec.v1.json"

# 2) Command workload
run "curl -sS -X POST '${SERVER_URL}/cmd/Ticket/create?tenant_id=${TENANT_ID}' -H 'content-type: application/json' -d '{\"input\":{\"id\":\"T-1\",\"title\":\"Pilot ticket\"}}'"
run "curl -sS -X POST '${SERVER_URL}/cmd/Ticket/triage?tenant_id=${TENANT_ID}' -H 'content-type: application/json' -d '{\"input\":{\"id\":\"T-1\"}}'"

# 3) View and verify checks
run "curl -sS '${SERVER_URL}/view/tickets_by_lane?tenant_id=${TENANT_ID}'"
run "curl -sS '${SERVER_URL}/verify?tenant_id=${TENANT_ID}'"
