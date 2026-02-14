#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
"${ROOT_DIR}/control-plane/scripts/collab_require_root.sh" "${ROOT_DIR}"

MODEL_FILE="${ROOT_DIR}/control-plane/collaboration/role-model.yaml"
SCHEMA_FILE="${ROOT_DIR}/control-plane/collaboration/role-model.schema.json"

cd "${ROOT_DIR}"

# Validate schema exists
if [[ ! -f "${SCHEMA_FILE}" ]]; then
  echo "role-model: FAIL - schema not found: ${SCHEMA_FILE}" >&2
  exit 1
fi

# Validate model exists
if [[ ! -f "${MODEL_FILE}" ]]; then
  echo "role-model: FAIL - model not found: ${MODEL_FILE}" >&2
  exit 1
fi

# Validate YAML is parseable
if ! python3 -c "import yaml; yaml.safe_load(open('${MODEL_FILE}'))" 2>/dev/null; then
  echo "role-model: FAIL - invalid YAML" >&2
  exit 1
fi

# Validate JSON schema is parseable
if ! python3 -c "import json; json.load(open('${SCHEMA_FILE}'))" 2>/dev/null; then
  echo "role-model: FAIL - invalid JSON schema" >&2
  exit 1
fi

# Structural validation
python3 - "${MODEL_FILE}" <<'PY'
import sys
import yaml
from pathlib import Path

doc = yaml.safe_load(Path(sys.argv[1]).read_text())
errors = []

# Required fields
if "version" not in doc:
  errors.append("missing version")
if "roles" not in doc or not doc["roles"]:
  errors.append("missing or empty roles")
if "authority_matrix" not in doc or not doc["authority_matrix"]:
  errors.append("missing or empty authority_matrix")

# Role validation
if "roles" in doc:
  role_ids = set()
  for role in doc["roles"]:
    rid = role.get("id", "")
    if not rid:
      errors.append("role missing id")
    elif rid in role_ids:
      errors.append(f"duplicate role id: {rid}")
    else:
      role_ids.add(rid)
    
    if "authorities" not in role:
      errors.append(f"role {rid} missing authorities")
    if "proactive" not in role:
      errors.append(f"role {rid} missing proactive flag")

# Authority matrix validation
if "authority_matrix" in doc:
  decisions = set()
  for entry in doc["authority_matrix"]:
    d = entry.get("decision", "")
    if not d:
      errors.append("authority_matrix entry missing decision")
    elif d in decisions:
      errors.append(f"duplicate decision in matrix: {d}")
    else:
      decisions.add(d)
    
    if "decision_ref" not in entry:
      errors.append(f"decision {d} missing decision_ref")
    if "authority" not in entry:
      errors.append(f"decision {d} missing authority")
    elif entry["authority"] not in ("main", "worker", "shared"):
      errors.append(f"decision {d} has invalid authority: {entry['authority']}")

# Must have main and worker roles
if "roles" in doc:
  role_ids = {r.get("id") for r in doc["roles"]}
  if "main" not in role_ids:
    errors.append("missing required role: main")
  if "worker" not in role_ids:
    errors.append("missing required role: worker")

if errors:
  print("role-model: FAIL")
  for e in errors:
    print(f"  - {e}")
  sys.exit(1)
else:
  print("role-model: PASS")
  print(f"  Roles: {len(doc.get('roles', []))}")
  print(f"  Authority entries: {len(doc.get('authority_matrix', []))}")
  sys.exit(0)
PY
