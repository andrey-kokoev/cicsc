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
    collab = load_yaml("control-plane/collaboration/collab-model.yaml")
    execution = load_yaml("control-plane/execution/execution-ledger.yaml")
    gate = load_yaml("control-plane/gates/gate-model.yaml")

    objective_ids = {o.get("id") for o in objective.get("objectives", [])}
    capability_ids = {c.get("id") for c in capability.get("capabilities", [])}
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

    claim_kind_ids = {c.get("id") for c in collab.get("claim_kinds", [])}
    evidence_kind_ids = {e.get("id") for e in collab.get("evidence_kinds", [])}
    obligation_ids = {o.get("id") for o in collab.get("obligation_profiles", [])}
    message_kind_ids = {m.get("id") for m in collab.get("message_kinds", [])}

    for ck in collab.get("claim_kinds", []):
        for ref in ck.get("required_obligation_profile_refs", []):
            if ref not in obligation_ids:
                errors.append(f"collab-model: claim kind {ck.get('id')} unknown obligation ref {ref}")

    for op in collab.get("obligation_profiles", []):
        for ref in op.get("claim_kind_refs", []):
            if ref not in claim_kind_ids:
                errors.append(f"collab-model: obligation {op.get('id')} unknown claim kind ref {ref}")
        for req_ev in op.get("required_evidence", []):
            ref = req_ev.get("evidence_kind_ref")
            if ref not in evidence_kind_ids:
                errors.append(f"collab-model: obligation {op.get('id')} unknown evidence kind ref {ref}")
        for script in op.get("required_scripts", []):
            if isinstance(script, str) and not path_exists(script):
                errors.append(f"collab-model: obligation {op.get('id')} missing required script {script}")

    for eb in collab.get("execution_bindings", []):
        oref = eb.get("objective_ref")
        cref = eb.get("capability_ref")
        if oref not in objective_ids:
            errors.append(f"collab-model: execution binding unknown objective ref {oref}")
        if cref not in capability_ids:
            errors.append(f"collab-model: execution binding unknown capability ref {cref}")
        for ref in eb.get("claim_kind_refs", []):
            if ref not in claim_kind_ids:
                errors.append(f"collab-model: execution binding unknown claim kind ref {ref}")

    handoff = collab.get("handoff_protocol", {})
    branch_pattern = handoff.get("branch_pattern")
    branch_re = None
    if isinstance(branch_pattern, str):
        try:
            branch_re = re.compile(branch_pattern)
        except re.error as exc:
            errors.append(f"collab-model: invalid handoff branch_pattern regex: {exc}")

    agent_map = {}
    for agent in collab.get("agents", []):
        aid = agent.get("id")
        if aid in agent_map:
            errors.append(f"collab-model: duplicate agent id {aid}")
        else:
            agent_map[aid] = agent

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
        phase_done = 0
        phase_open = 0

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
                cstatus = cb.get("status")
                if cstatus == "done":
                    phase_done += 1
                elif cstatus == "open":
                    phase_open += 1

        pstatus = ph.get("status")
        if pstatus == "complete" and phase_open > 0:
            errors.append(f"execution-ledger: phase {pid} marked complete but has open checkboxes")
        if pstatus == "planned" and phase_done > 0:
            errors.append(f"execution-ledger: phase {pid} marked planned but has done checkboxes")

    for eb in collab.get("execution_bindings", []):
        for cbref in eb.get("ledger_checkbox_refs", []):
            if cbref not in seen_checkbox_ids:
                errors.append(f"collab-model: execution binding unknown ledger checkbox ref {cbref}")

    for script in handoff.get("required_gate_scripts", []):
        if isinstance(script, str) and not path_exists(script):
            errors.append(f"collab-model: handoff protocol missing gate script {script}")

    checkbox_status = {}
    for ph in execution.get("phases", []):
        for ms in ph.get("milestones", []):
            for cb in ms.get("checkboxes", []):
                checkbox_status[cb.get("id")] = cb.get("status")

    active_assignment_statuses = {"assigned", "in_progress", "submitted"}
    assignment_map = {}
    active_by_checkbox = {}
    for a in collab.get("assignments", []):
        aid = a.get("id")
        agent_ref = a.get("agent_ref")
        checkbox_ref = a.get("checkbox_ref")
        claim_kind_ref = a.get("claim_kind_ref")
        worktree = a.get("worktree")
        branch = a.get("branch")
        astatus = a.get("status")
        assignment_map[aid] = a

        if agent_ref not in agent_map:
            errors.append(f"collab-model: assignment {aid} unknown agent_ref {agent_ref}")
        else:
            expected_worktree = agent_map[agent_ref].get("worktree")
            if expected_worktree != worktree:
                errors.append(
                    f"collab-model: assignment {aid} worktree mismatch (got {worktree}, expected {expected_worktree})"
                )

        if checkbox_ref not in checkbox_status:
            errors.append(f"collab-model: assignment {aid} unknown checkbox_ref {checkbox_ref}")
        if claim_kind_ref not in claim_kind_ids:
            errors.append(f"collab-model: assignment {aid} unknown claim_kind_ref {claim_kind_ref}")
        if branch_re and isinstance(branch, str) and not branch_re.match(branch):
            errors.append(f"collab-model: assignment {aid} branch {branch} violates handoff branch_pattern")

        cb_status = checkbox_status.get(checkbox_ref)
        if cb_status == "done" and astatus in active_assignment_statuses:
            errors.append(
                f"collab-model: assignment {aid} active but checkbox {checkbox_ref} is already done"
            )
        if astatus in active_assignment_statuses:
            prev = active_by_checkbox.get(checkbox_ref)
            if prev:
                errors.append(
                    f"collab-model: multiple active assignments for checkbox {checkbox_ref}: {prev}, {aid}"
                )
            else:
                active_by_checkbox[checkbox_ref] = aid

    def maybe_path_ref(ref: str) -> bool:
        return (
            ref.startswith("docs/")
            or ref.startswith("scripts/")
            or ref.startswith("control-plane/")
            or ref.startswith("lean/")
        )

    seen_message_ids = set()
    for msg in collab.get("messages", []):
        mid = msg.get("id")
        if mid in seen_message_ids:
            errors.append(f"collab-model: duplicate message id {mid}")
        seen_message_ids.add(mid)

        kind_ref = msg.get("kind_ref")
        assignment_ref = msg.get("assignment_ref")
        from_agent_ref = msg.get("from_agent_ref")
        to_agent_ref = msg.get("to_agent_ref")
        from_worktree = msg.get("from_worktree")
        to_worktree = msg.get("to_worktree")
        branch = msg.get("branch")

        if kind_ref not in message_kind_ids:
            errors.append(f"collab-model: message {mid} unknown kind_ref {kind_ref}")
        if assignment_ref not in assignment_map:
            errors.append(f"collab-model: message {mid} unknown assignment_ref {assignment_ref}")
            continue

        if from_agent_ref not in agent_map:
            errors.append(f"collab-model: message {mid} unknown from_agent_ref {from_agent_ref}")
        else:
            expected = agent_map[from_agent_ref].get("worktree")
            if expected != from_worktree:
                errors.append(
                    f"collab-model: message {mid} from_worktree mismatch (got {from_worktree}, expected {expected})"
                )

        if to_agent_ref not in agent_map:
            errors.append(f"collab-model: message {mid} unknown to_agent_ref {to_agent_ref}")
        else:
            expected = agent_map[to_agent_ref].get("worktree")
            if expected != to_worktree:
                errors.append(
                    f"collab-model: message {mid} to_worktree mismatch (got {to_worktree}, expected {expected})"
                )

        assignment = assignment_map[assignment_ref]
        if assignment.get("agent_ref") != to_agent_ref:
            errors.append(
                f"collab-model: message {mid} to_agent_ref {to_agent_ref} does not match assignment agent_ref {assignment.get('agent_ref')}"
            )
        if assignment.get("branch") != branch:
            errors.append(
                f"collab-model: message {mid} branch {branch} does not match assignment branch {assignment.get('branch')}"
            )

        if branch_re and isinstance(branch, str) and not branch_re.match(branch):
            errors.append(f"collab-model: message {mid} branch {branch} violates handoff branch_pattern")

        for ref in msg.get("payload_refs", []):
            if isinstance(ref, str) and maybe_path_ref(ref) and not path_exists(ref):
                errors.append(f"collab-model: message {mid} missing payload ref {ref}")
        for ref in msg.get("evidence_refs", []):
            if isinstance(ref, str) and maybe_path_ref(ref) and not path_exists(ref):
                errors.append(f"collab-model: message {mid} missing evidence ref {ref}")

    seen_gate_ids = set()
    seen_gate_scripts = set()
    for g in gate.get("gates", []):
        gid = g.get("id")
        if gid in seen_gate_ids:
            errors.append(f"gate-model: duplicate gate id {gid}")
        seen_gate_ids.add(gid)
        req = g.get("required_scripts", [])
        if not req:
            errors.append(f"gate-model: gate {gid} has no required_scripts")
        for script in req:
            if isinstance(script, str) and not path_exists(script):
                errors.append(f"gate-model: missing required script {script}")
            if script in seen_gate_scripts:
                errors.append(f"gate-model: duplicate script in execution order {script}")
            seen_gate_scripts.add(script)

    if errors:
        print("cross-model validation failed", file=sys.stderr)
        for e in errors:
            print(f"- {e}", file=sys.stderr)
        return 1

    print("cross-model validation passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
