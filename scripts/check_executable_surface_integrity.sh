#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

JSON_OUT=""
POLICY_PATH="control-plane/gates/executable-surface-policy.json"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --json)
            JSON_OUT="${2:-}"
            shift 2
            ;;
        --policy)
            POLICY_PATH="${2:-}"
            shift 2
            ;;
        --help|-h)
            echo "Usage: $0 [--json <path>] [--policy <path>]"
            exit 0
            ;;
        *)
            echo "Unknown arg: $1" >&2
            echo "Usage: $0 [--json <path>] [--policy <path>]" >&2
            exit 1
            ;;
    esac
done

python3 - "$POLICY_PATH" "$JSON_OUT" <<'PY'
from __future__ import annotations

import datetime as dt
import fnmatch
import json
import re
import sys
from pathlib import Path


ROOT = Path(".").resolve()
policy_path = Path(sys.argv[1])
json_out = sys.argv[2] if len(sys.argv) > 2 else ""

if not policy_path.is_absolute():
    policy_path = ROOT / policy_path

if not policy_path.exists():
    print(f"executable surface integrity check failed")
    print(f"- missing policy file: {policy_path.relative_to(ROOT)}")
    raise SystemExit(1)

policy = json.loads(policy_path.read_text(encoding="utf-8"))


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def parse_date(value: str) -> dt.date | None:
    try:
        return dt.date.fromisoformat(value)
    except Exception:
        return None


def list_scope_files() -> list[Path]:
    include = policy.get("scope", {}).get("include_globs", [])
    exclude = policy.get("scope", {}).get("exclude_globs", [])
    paths: set[Path] = set()
    for glob in include:
        for p in ROOT.glob(glob):
            if not p.is_file():
                continue
            rp = rel(p)
            if any(fnmatch.fnmatch(rp, ex) for ex in exclude):
                continue
            paths.add(p.resolve())
    return sorted(paths)


QUOTED_RE = re.compile(r"""(['"])([^'"]*[/.][^'"]*)\1""")
TOKEN_RE = re.compile(r"(?<![A-Za-z0-9_])((?:\./|\../)?[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)+)")


def line_is_comment(file_path: Path, line: str) -> bool:
    stripped = line.strip()
    ext = file_path.suffix
    if ext in {".sh", ".py"}:
        return stripped.startswith("#")
    if ext in {".ts", ".tsx", ".js", ".jsx"}:
        return (
            stripped.startswith("//")
            or stripped.startswith("/*")
            or stripped.startswith("*")
            or stripped.startswith("*/")
        )
    return False


def clean_ref(raw: str) -> str:
    out = raw.strip()
    out = out.lstrip("(")
    out = out.rstrip("),;:")
    return out


def is_candidate_ref(candidate: str) -> bool:
    if not candidate:
        return False
    if any(ch.isspace() for ch in candidate):
        return False
    if "://" in candidate:
        return False
    if any(x in candidate for x in ["${", "$(", "`", "<", ">", "*"]):
        return False
    if candidate.startswith("$"):
        return False
    if candidate.startswith("node:"):
        return False
    if candidate.startswith("app://"):
        return False
    return "/" in candidate


ROOT_ENTRIES = {p.name for p in ROOT.iterdir()}


def normalize_reference(reference: str, source_file: Path) -> str | None:
    if reference.startswith("/"):
        return None

    if reference.startswith("./") or reference.startswith("../"):
        source_resolved = (source_file.parent / reference).resolve()
        root_resolved = (ROOT / reference.lstrip("./")).resolve()

        for resolved in (source_resolved, root_resolved):
            try:
                rel_path = resolved.relative_to(ROOT).as_posix()
            except ValueError:
                continue
            if (ROOT / rel_path).exists():
                return rel_path

        if reference.startswith("./"):
            return reference[2:]
        try:
            return source_resolved.relative_to(ROOT).as_posix()
        except ValueError:
            return None

    first = reference.split("/", 1)[0]
    if first not in ROOT_ENTRIES:
        return None
    return reference.lstrip("./")


def extract_refs(file_path: Path) -> list[tuple[int, str]]:
    refs: list[tuple[int, str]] = []
    for idx, line in enumerate(file_path.read_text(encoding="utf-8", errors="replace").splitlines(), start=1):
        if line_is_comment(file_path, line):
            continue

        seen: set[str] = set()
        for m in QUOTED_RE.finditer(line):
            cand = clean_ref(m.group(2))
            if is_candidate_ref(cand) and cand not in seen:
                refs.append((idx, cand))
                seen.add(cand)
        for m in TOKEN_RE.finditer(line):
            cand = clean_ref(m.group(1))
            if is_candidate_ref(cand) and cand not in seen:
                refs.append((idx, cand))
                seen.add(cand)
    return refs


banned_patterns = [re.compile(p) for p in policy.get("banned_reference_patterns", [])]
generated_contracts = policy.get("generated_contracts", [])
allowlist = policy.get("allowlist", [])
today = dt.date.today()

required_allowlist_fields = ("kind", "source_file", "reference", "owner", "reason", "expires_on")
valid_allowlist_indices: set[int] = set()
allowlist_field_errors: dict[int, str] = {}

for idx, entry in enumerate(allowlist):
    missing = [k for k in required_allowlist_fields if not str(entry.get(k, "")).strip()]
    if missing:
        allowlist_field_errors[idx] = (
            f"allowlist entry missing required field(s): {', '.join(missing)}"
        )
        continue
    valid_allowlist_indices.add(idx)


def find_generated_contract(norm_path: str) -> dict | None:
    for c in generated_contracts:
        pat = c.get("artifact_pattern", "")
        if pat and fnmatch.fnmatch(norm_path, pat):
            return c
    return None


violations: list[dict] = []
raw_violations: list[dict] = []

for path in list_scope_files():
    source = rel(path)
    for line_no, reference in extract_refs(path):
        norm = normalize_reference(reference, path)

        for pat in banned_patterns:
            if pat.search(reference) or (norm and pat.search(norm)):
                raw_violations.append(
                    {
                        "kind": "non_canonical_runtime_source",
                        "source_file": source,
                        "line": line_no,
                        "reference": reference,
                        "normalized_path": norm,
                        "reason": "reference matches banned runtime source pattern",
                    }
                )
                break

        if norm and ".generated." in norm:
            contract = find_generated_contract(norm)
            if contract is None:
                raw_violations.append(
                    {
                        "kind": "generated_ref_without_contract",
                        "source_file": source,
                        "line": line_no,
                        "reference": reference,
                        "normalized_path": norm,
                        "reason": "generated artifact reference has no declared generator contract",
                    }
                )
            else:
                gen_cmd = str(contract.get("generator_command", "")).strip()
                gen_path = str(contract.get("generator_path", "")).strip()
                gen_path_exists = bool(gen_path) and (ROOT / gen_path).exists()
                if not gen_cmd or not gen_path_exists:
                    raw_violations.append(
                        {
                            "kind": "generated_ref_without_contract",
                            "source_file": source,
                            "line": line_no,
                            "reference": reference,
                            "normalized_path": norm,
                            "reason": "generated contract is invalid (missing command or generator path)",
                        }
                    )
            continue

        if norm is None:
            continue

        # Missing-path checks apply to executable script references only.
        if not (norm.endswith(".sh") or norm.endswith(".py")):
            continue

        if not (ROOT / norm).exists():
            raw_violations.append(
                {
                    "kind": "missing_path",
                    "source_file": source,
                    "line": line_no,
                    "reference": reference,
                    "normalized_path": norm,
                    "reason": "referenced path does not exist",
                }
            )


def allowlist_match(v: dict, entry: dict) -> bool:
    return (
        v["kind"] == entry.get("kind")
        and v["source_file"] == entry.get("source_file")
        and v["reference"] == entry.get("reference")
    )


matched_allowlist_indices: set[int] = set()

for v in raw_violations:
    allowlisted = False
    expires = None
    for idx, entry in enumerate(allowlist):
        if idx not in valid_allowlist_indices:
            continue
        exp = parse_date(str(entry.get("expires_on", "")))
        if exp is None:
            continue
        if exp < today:
            continue
        if allowlist_match(v, entry):
            allowlisted = True
            expires = entry.get("expires_on")
            matched_allowlist_indices.add(idx)
            break

    item = dict(v)
    item["allowlisted"] = allowlisted
    item["allowlist_expires_on"] = expires
    violations.append(item)


for idx, entry in enumerate(allowlist):
    if idx in allowlist_field_errors:
        violations.append(
            {
                "kind": "stale_allowlist_entry",
                "source_file": str(entry.get("source_file") or ""),
                "line": None,
                "reference": str(entry.get("reference") or ""),
                "normalized_path": None,
                "reason": allowlist_field_errors[idx],
                "allowlisted": False,
                "allowlist_expires_on": str(entry.get("expires_on") or ""),
            }
        )
        continue

    exp_raw = str(entry.get("expires_on", ""))
    exp = parse_date(exp_raw)
    if exp is None:
        violations.append(
            {
                "kind": "stale_allowlist_entry",
                "source_file": str(entry.get("source_file") or ""),
                "line": None,
                "reference": str(entry.get("reference") or ""),
                "normalized_path": None,
                "reason": "allowlist entry has invalid expires_on date",
                "allowlisted": False,
                "allowlist_expires_on": exp_raw,
            }
        )
        continue
    if exp < today:
        violations.append(
            {
                "kind": "stale_allowlist_entry",
                "source_file": str(entry.get("source_file") or ""),
                "line": None,
                "reference": str(entry.get("reference") or ""),
                "normalized_path": None,
                "reason": "allowlist entry is expired",
                "allowlisted": False,
                "allowlist_expires_on": exp_raw,
            }
        )
        continue
    if idx not in matched_allowlist_indices:
        violations.append(
            {
                "kind": "stale_allowlist_entry",
                "source_file": str(entry.get("source_file") or ""),
                "line": None,
                "reference": str(entry.get("reference") or ""),
                "normalized_path": None,
                "reason": "allowlist entry does not match any current violation",
                "allowlisted": False,
                "allowlist_expires_on": exp_raw,
            }
        )


report = {
    "version": "cicsc/executable-surface-integrity-v1",
    "policy": rel(policy_path),
    "violations": violations,
}

if json_out:
    out = Path(json_out)
    if not out.is_absolute():
        out = ROOT / out
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

hard_fail = [v for v in violations if not v.get("allowlisted", False)]

if not hard_fail:
    print("executable surface integrity check passed")
    raise SystemExit(0)

print("executable surface integrity check failed")
for v in hard_fail:
    line = f":{v['line']}" if v.get("line") else ""
    print(
        f"- {v['kind']} {v.get('source_file','')}{line} "
        f"ref={v.get('reference','')} reason={v.get('reason','')}"
    )
raise SystemExit(1)
PY
