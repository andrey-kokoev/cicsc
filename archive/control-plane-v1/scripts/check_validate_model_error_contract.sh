#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "${ROOT_DIR}"

tmpdir="$(mktemp -d)"
trap 'rm -rf "${tmpdir}"' EXIT

bad_yaml_model="${tmpdir}/bad.yaml"
echo "messages: [" >"${bad_yaml_model}"

minimal_schema="${tmpdir}/minimal.schema.json"
cat >"${minimal_schema}" <<'JSON'
{
  "type": "object"
}
JSON

set +e
yaml_err="$(
  ./control-plane/scripts/validate_model.py "${bad_yaml_model}" "${minimal_schema}" 2>&1
)"
yaml_code=$?
set -e
if [[ ${yaml_code} -eq 0 ]]; then
  echo "expected invalid yaml validation failure, got success"
  exit 1
fi
if ! grep -Eq "bad\\.yaml:[0-9]+(:[0-9]+)?: invalid yaml:" <<<"${yaml_err}"; then
  echo "expected file:line invalid yaml format, got:"
  echo "${yaml_err}"
  exit 1
fi
if ! grep -Fq "hint: fix YAML syntax" <<<"${yaml_err}"; then
  echo "expected actionable hint for yaml failure, got:"
  echo "${yaml_err}"
  exit 1
fi

mismatch_model="${tmpdir}/mismatch.yaml"
cat >"${mismatch_model}" <<'YAML'
name: 123
YAML

mismatch_schema="${tmpdir}/mismatch.schema.json"
cat >"${mismatch_schema}" <<'JSON'
{
  "type": "object",
  "required": ["name"],
  "properties": {
    "name": { "type": "string" }
  },
  "additionalProperties": false
}
JSON

set +e
schema_err="$(
  ./control-plane/scripts/validate_model.py "${mismatch_model}" "${mismatch_schema}" 2>&1
)"
schema_code=$?
set -e
if [[ ${schema_code} -eq 0 ]]; then
  echo "expected schema mismatch failure, got success"
  exit 1
fi
if ! grep -Eq "mismatch\\.yaml:1: schema validation failed:" <<<"${schema_err}"; then
  echo "expected file:line schema failure format, got:"
  echo "${schema_err}"
  exit 1
fi
if ! grep -Fq "path=name" <<<"${schema_err}"; then
  echo "expected schema path hint, got:"
  echo "${schema_err}"
  exit 1
fi
if ! grep -Fq "hint: check required fields/types" <<<"${schema_err}"; then
  echo "expected actionable hint for schema failure, got:"
  echo "${schema_err}"
  exit 1
fi

echo "validate_model error contract check passed"
