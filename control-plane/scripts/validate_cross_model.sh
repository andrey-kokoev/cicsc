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
    claim_kind_map = {c.get("id"): c for c in collab.get("claim_kinds", [])}
    evidence_kind_ids = {e.get("id") for e in collab.get("evidence_kinds", [])}
    obligation_ids = {o.get("id") for o in collab.get("obligation_profiles", [])}
    obligation_map = {o.get("id"): o for o in collab.get("obligation_profiles", [])}
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
    worktree_owner_map = {}
    for agent in collab.get("agents", []):
        aid = agent.get("id")
        wt = agent.get("worktree")
        if aid in agent_map:
            errors.append(f"collab-model: duplicate agent id {aid}")
        else:
            agent_map[aid] = agent
        if wt in worktree_owner_map and worktree_owner_map[wt] != aid:
            errors.append(
                f"collab-model: worktree {wt} has multiple owners ({worktree_owner_map[wt]}, {aid}) under single-owner semantics"
            )
        else:
            worktree_owner_map[wt] = aid

    worktree_gov = collab.get("worktree_governance", {})
    ownership_mode = worktree_gov.get("ownership_mode")
    assignment_dispatch_kind_ref = worktree_gov.get("assignment_dispatch_kind_ref")
    enforce_owner_dispatch = bool(worktree_gov.get("enforce_owner_dispatch"))
    canonical_worker_root = worktree_gov.get("canonical_worker_worktree_root")
    enforce_worker_root = bool(worktree_gov.get("enforce_canonical_worker_worktree_root"))
    creation_authorities = worktree_gov.get("worktree_creation_authority_agent_refs", [])
    if ownership_mode != "single_owner":
        errors.append(f"collab-model: unsupported ownership_mode {ownership_mode}")
    for aid in creation_authorities:
        if aid not in agent_map:
            errors.append(f"collab-model: unknown worktree creation authority agent {aid}")
    if enforce_worker_root and (not isinstance(canonical_worker_root, str) or not canonical_worker_root):
        errors.append("collab-model: canonical_worker_worktree_root must be set when enforcement is enabled")

    if enforce_worker_root and isinstance(canonical_worker_root, str):
        root_prefix = canonical_worker_root.rstrip("/") + "/"
        for aid, a in agent_map.items():
            if aid == "AGENT_MAIN":
                continue
            wt = a.get("worktree")
            if not isinstance(wt, str) or not wt.startswith(root_prefix):
                errors.append(
                    f"collab-model: agent {aid} worktree {wt} violates canonical worker root {canonical_worker_root}"
                )

    delegations = collab.get("worktree_delegations", [])
    active_delegation_by_worktree = {}
    for d in delegations:
        did = d.get("id")
        wt = d.get("worktree")
        owner_ref = d.get("owner_agent_ref")
        delegated_to = d.get("delegated_to_agent_ref")
        dstatus = d.get("status")
        dcommit = d.get("commit")

        if owner_ref not in agent_map:
            errors.append(f"collab-model: delegation {did} unknown owner_agent_ref {owner_ref}")
            continue
        if delegated_to not in agent_map:
            errors.append(f"collab-model: delegation {did} unknown delegated_to_agent_ref {delegated_to}")
            continue
        if owner_ref == delegated_to:
            errors.append(f"collab-model: delegation {did} owner and delegated_to must differ")
        if wt not in worktree_owner_map:
            errors.append(f"collab-model: delegation {did} unknown worktree {wt}")
        else:
            baseline_owner = worktree_owner_map[wt]
            if baseline_owner != owner_ref:
                errors.append(
                    f"collab-model: delegation {did} owner_agent_ref {owner_ref} does not match baseline owner {baseline_owner}"
                )
        if not isinstance(dcommit, str) or not re.fullmatch(r"[0-9a-f]{7,40}", dcommit):
            errors.append(f"collab-model: delegation {did} invalid commit {dcommit}")
        if dstatus == "active":
            if wt in active_delegation_by_worktree:
                errors.append(
                    f"collab-model: multiple active delegations for worktree {wt}: {active_delegation_by_worktree[wt].get('id')}, {did}"
                )
            else:
                active_delegation_by_worktree[wt] = d

    effective_owner_by_worktree = dict(worktree_owner_map)
    for wt, d in active_delegation_by_worktree.items():
        effective_owner_by_worktree[wt] = d.get("delegated_to_agent_ref")

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

    transition_policy = collab.get("message_transition_policy", {})
    initial_statuses = set(transition_policy.get("initial_statuses", []))
    terminal_statuses = set(transition_policy.get("terminal_statuses", []))
    allowed_transitions = {
        (t.get("from"), t.get("to"))
        for t in transition_policy.get("allowed_transitions", [])
    }
    policy_statuses = initial_statuses | terminal_statuses | {to for _, to in allowed_transitions} | {
        frm for frm, _ in allowed_transitions
    }

    messages = collab.get("messages", [])
    message_map = {}
    messages_by_assignment = {}
    seen_message_ids = set()
    for msg in messages:
        mid = msg.get("id")
        if mid in seen_message_ids:
            errors.append(f"collab-model: duplicate message id {mid}")
        seen_message_ids.add(mid)
        message_map[mid] = msg
        aref = msg.get("assignment_ref")
        if isinstance(aref, str):
            messages_by_assignment.setdefault(aref, []).append(mid)

    commit_re = re.compile(r"^[0-9a-f]{7,40}$")
    digest_re = re.compile(r"^sha256:[0-9a-f]{64}$")
    for msg in messages:
        mid = msg.get("id")
        kind_ref = msg.get("kind_ref")
        assignment_ref = msg.get("assignment_ref")
        from_agent_ref = msg.get("from_agent_ref")
        to_agent_ref = msg.get("to_agent_ref")
        from_worktree = msg.get("from_worktree")
        to_worktree = msg.get("to_worktree")
        branch = msg.get("branch")
        initial_status = msg.get("initial_status")
        supersedes = msg.get("supersedes_message_ref")

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
        if (
            enforce_owner_dispatch
            and kind_ref == assignment_dispatch_kind_ref
            and from_worktree in effective_owner_by_worktree
            and effective_owner_by_worktree[from_worktree] != from_agent_ref
        ):
            errors.append(
                f"collab-model: message {mid} dispatch authority mismatch; {from_agent_ref} is not effective owner of {from_worktree}"
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

        if initial_status not in initial_statuses:
            errors.append(
                f"collab-model: message {mid} initial_status {initial_status} must be in initial_statuses"
            )

        for ref in msg.get("payload_refs", []):
            if isinstance(ref, str) and maybe_path_ref(ref) and not path_exists(ref):
                errors.append(f"collab-model: message {mid} missing payload ref {ref}")
        for ref in msg.get("evidence_refs", []):
            if isinstance(ref, str) and maybe_path_ref(ref) and not path_exists(ref):
                errors.append(f"collab-model: message {mid} missing evidence ref {ref}")
        for ev in msg.get("evidence_bindings", []):
            ref = ev.get("ref")
            evidence_kind_ref = ev.get("evidence_kind_ref")
            commit = ev.get("commit")
            digest = ev.get("digest")
            if isinstance(ref, str) and maybe_path_ref(ref) and not path_exists(ref):
                errors.append(f"collab-model: message {mid} missing evidence binding ref {ref}")
            if evidence_kind_ref not in evidence_kind_ids:
                errors.append(f"collab-model: message {mid} invalid evidence kind ref {evidence_kind_ref}")
            if not isinstance(commit, str) or not commit_re.match(commit):
                errors.append(f"collab-model: message {mid} invalid evidence commit {commit}")
            if not isinstance(digest, str) or not digest_re.match(digest):
                errors.append(f"collab-model: message {mid} invalid evidence digest {digest}")

        if supersedes:
            if supersedes == mid:
                errors.append(f"collab-model: message {mid} supersedes itself")
            elif supersedes not in message_map:
                errors.append(f"collab-model: message {mid} unknown supersedes_message_ref {supersedes}")
            else:
                old = message_map[supersedes]
                if old.get("assignment_ref") != assignment_ref:
                    errors.append(
                        f"collab-model: message {mid} supersedes {supersedes} with different assignment_ref"
                    )
                if old.get("to_agent_ref") != to_agent_ref:
                    errors.append(
                        f"collab-model: message {mid} supersedes {supersedes} with different to_agent_ref"
                    )

    events = collab.get("message_events", [])
    events_by_message = {}
    terminal_status_by_message = {}
    saw_fulfilled_by_message = {}
    fulfilled_events_by_message = {}
    seen_event_ids = set()
    for ev in events:
        eid = ev.get("id")
        if eid in seen_event_ids:
            errors.append(f"collab-model: duplicate message event id {eid}")
        seen_event_ids.add(eid)
        mref = ev.get("message_ref")
        if mref not in message_map:
            errors.append(f"collab-model: message event {eid} unknown message_ref {mref}")
            continue
        events_by_message.setdefault(mref, []).append(ev)

    for mid, msg in message_map.items():
        m_events = sorted(events_by_message.get(mid, []), key=lambda e: e.get("at_seq", 0))
        if not m_events:
            errors.append(f"collab-model: message {mid} has no message_events")
            continue

        seen_seq = set()
        expected_prev = None
        saw_fulfilled = False
        for idx, ev in enumerate(m_events):
            eid = ev.get("id")
            from_status = ev.get("from_status")
            to_status = ev.get("to_status")
            actor = ev.get("actor_agent_ref")
            at_seq = ev.get("at_seq")
            commit = ev.get("commit")

            if at_seq in seen_seq:
                errors.append(f"collab-model: message {mid} duplicate event at_seq {at_seq}")
            seen_seq.add(at_seq)

            if actor not in agent_map:
                errors.append(f"collab-model: message event {eid} unknown actor_agent_ref {actor}")
            if not isinstance(commit, str) or not commit_re.match(commit):
                errors.append(f"collab-model: message event {eid} invalid commit {commit}")

            for bind in ev.get("evidence_bindings", []):
                ref = bind.get("ref")
                evidence_kind_ref = bind.get("evidence_kind_ref")
                bcommit = bind.get("commit")
                digest = bind.get("digest")
                if isinstance(ref, str) and maybe_path_ref(ref) and not path_exists(ref):
                    errors.append(f"collab-model: message event {eid} missing evidence binding ref {ref}")
                if evidence_kind_ref not in evidence_kind_ids:
                    errors.append(
                        f"collab-model: message event {eid} invalid evidence kind ref {evidence_kind_ref}"
                    )
                if not isinstance(bcommit, str) or not commit_re.match(bcommit):
                    errors.append(f"collab-model: message event {eid} invalid evidence commit {bcommit}")
                if not isinstance(digest, str) or not digest_re.match(digest):
                    errors.append(f"collab-model: message event {eid} invalid evidence digest {digest}")

            if idx == 0:
                if from_status is not None:
                    errors.append(f"collab-model: first event for message {mid} must have from_status null")
                if to_status != msg.get("initial_status"):
                    errors.append(
                        f"collab-model: first event for message {mid} to_status {to_status} must equal initial_status {msg.get('initial_status')}"
                    )
                expected_prev = to_status
            else:
                if from_status != expected_prev:
                    errors.append(
                        f"collab-model: message event {eid} from_status {from_status} does not match previous to_status {expected_prev}"
                    )
                if (from_status, to_status) not in allowed_transitions:
                    errors.append(
                        f"collab-model: message event {eid} illegal transition {from_status} -> {to_status}"
                    )
                if from_status in terminal_statuses:
                    errors.append(f"collab-model: message event {eid} transition from terminal status {from_status}")
                expected_prev = to_status

            if to_status == "rescinded":
                if not ev.get("rescinded_reason"):
                    errors.append(f"collab-model: message event {eid} rescinded but missing rescinded_reason")
                if from_status not in {"queued", "sent"}:
                    errors.append(
                        f"collab-model: message event {eid} rescinded from unsupported from_status {from_status}"
                    )
            if to_status == "fulfilled":
                saw_fulfilled = True
                fulfilled_events_by_message.setdefault(mid, []).append(ev)

        terminal_status_by_message[mid] = expected_prev
        saw_fulfilled_by_message[mid] = saw_fulfilled

    # WIP policy is enforced at claim-time by collab_claim_next.sh:
    # when acknowledged work exists for a worktree, claiming new actionable
    # messages is blocked unless force-overridden. Coexistence of
    # acknowledged + actionable in mailbox state is valid.

    for aid, assignment in assignment_map.items():
        astatus = assignment.get("status")
        outcome = assignment.get("outcome")
        mids = messages_by_assignment.get(aid, [])

        if not mids:
            errors.append(f"collab-model: assignment {aid} has no bound message")
            continue

        terminals = {terminal_status_by_message.get(mid) for mid in mids if mid in terminal_status_by_message}
        has_closed = "closed" in terminals
        has_rescinded = "rescinded" in terminals
        has_fulfilled = any(saw_fulfilled_by_message.get(mid, False) for mid in mids)

        if astatus in active_assignment_statuses and outcome != "pending":
            errors.append(
                f"collab-model: assignment {aid} active status {astatus} requires outcome pending (got {outcome})"
            )
        if astatus == "blocked" and outcome != "blocked":
            errors.append(
                f"collab-model: assignment {aid} blocked status requires outcome blocked (got {outcome})"
            )
        if astatus in {"done", "ingested"} and outcome == "pending":
            errors.append(
                f"collab-model: assignment {aid} terminal-ish status {astatus} cannot have pending outcome"
            )
        if has_closed and astatus in active_assignment_statuses:
            errors.append(
                f"collab-model: assignment {aid} has closed message but remains active ({astatus})"
            )
        if astatus == "done":
            if outcome == "fulfilled_by_assignee":
                if not (has_closed and has_fulfilled):
                    errors.append(
                        f"collab-model: assignment {aid} fulfilled_by_assignee requires closed terminal and fulfilled event"
                    )
                assignment_claim = assignment.get("claim_kind_ref")
                claim_cfg = claim_kind_map.get(assignment_claim) or {}
                profile_refs = claim_cfg.get("required_obligation_profile_refs", [])
                fulfilled_events = []
                for mid in mids:
                    fulfilled_events.extend(fulfilled_events_by_message.get(mid, []))
                fulfilled_by_assignee_events = [
                    ev for ev in fulfilled_events if ev.get("actor_agent_ref") == assignment.get("agent_ref")
                ]
                if not fulfilled_by_assignee_events:
                    errors.append(
                        f"collab-model: assignment {aid} has no fulfilled event by assigned agent for obligation discharge"
                    )
                evidence_bindings = []
                for ev in fulfilled_by_assignee_events:
                    evidence_bindings.extend(ev.get("evidence_bindings", []))
                evidence_kind_counts = {}
                for bind in evidence_bindings:
                    k = bind.get("evidence_kind_ref")
                    evidence_kind_counts[k] = evidence_kind_counts.get(k, 0) + 1
                for pref in profile_refs:
                    profile = obligation_map.get(pref)
                    if not profile:
                        errors.append(f"collab-model: assignment {aid} missing obligation profile {pref}")
                        continue
                    for req_ev in profile.get("required_evidence", []):
                        kind = req_ev.get("evidence_kind_ref")
                        min_count = req_ev.get("min_count", 0)
                        if evidence_kind_counts.get(kind, 0) < min_count:
                            errors.append(
                                f"collab-model: assignment {aid} does not satisfy required evidence {kind} (need {min_count})"
                            )
                    required_scripts = profile.get("required_scripts", [])
                    if required_scripts and evidence_kind_counts.get("EVID_SCRIPT", 0) < 1:
                        errors.append(
                            f"collab-model: assignment {aid} has required_scripts but no EVID_SCRIPT in fulfilled evidence"
                        )
            elif outcome == "fulfilled_by_main":
                if not has_rescinded:
                    errors.append(
                        f"collab-model: assignment {aid} fulfilled_by_main requires rescinded terminal message"
                    )
            elif outcome != "blocked":
                errors.append(f"collab-model: assignment {aid} done has unsupported outcome {outcome}")

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
