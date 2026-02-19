#!/usr/bin/env python3
"""Daemon runtime for control-plane worker execution."""

from __future__ import annotations

import argparse
import fcntl
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

import db


def _safe_agent_id(agent_id: str) -> str:
    return "".join(ch if ch.isalnum() or ch in "._-" else "_" for ch in agent_id)


def _state_paths(root: Path, agent_id: str) -> tuple[Path, Path, Path]:
    safe = _safe_agent_id(agent_id)
    state = root / "state"
    return (
        state / f"agentd-{safe}.lock",
        state / f"agentd-{safe}.pid",
        state / f"agentd-{safe}.stop",
    )


def _run_loop(root: Path, agent_id: str, poll_seconds: int, lease_seconds: int) -> int:
    lock_path, pid_path, stop_path = _state_paths(root, agent_id)
    lock_path.parent.mkdir(parents=True, exist_ok=True)

    lock_fd = os.open(str(lock_path), os.O_RDWR | os.O_CREAT, 0o644)
    try:
        fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        running_pid = "unknown"
        if pid_path.exists():
            running_pid = pid_path.read_text(encoding="utf-8").strip() or "unknown"
        print(f"agentd already running for {agent_id} (PID {running_pid}); exiting.")
        os.close(lock_fd)
        return 0

    pid = os.getpid()
    pid_path.write_text(f"{pid}\n", encoding="utf-8")
    if stop_path.exists():
        stop_path.unlink()

    stop_requested = False
    stop_reason = "stop_requested"

    def _signal_stop(signum: int, _frame: object) -> None:
        nonlocal stop_requested, stop_reason
        stop_requested = True
        stop_reason = f"signal_{signum}"

    signal.signal(signal.SIGINT, _signal_stop)
    signal.signal(signal.SIGTERM, _signal_stop)

    db.get_or_create_agent(agent_id)
    db.heartbeat_agent(agent_id, pid=pid, lease_seconds=lease_seconds)
    db.append_event("agent_started", agent_ref=agent_id, details={"pid": pid})

    print(f"=== agentd running for {agent_id} ===")
    print(f"PID: {pid}")
    print(f"poll_seconds={poll_seconds} lease_seconds={lease_seconds}")

    last_mode = ""
    try:
        while not stop_requested:
            if stop_path.exists():
                stop_requested = True
                stop_reason = "stop_requested"
                break

            assignment = db.heartbeat_agent(agent_id, pid=pid, lease_seconds=lease_seconds)
            snapshot = db.get_agent_snapshot(agent_id)
            status = str(snapshot.get("status") or "unknown")

            if status == "blocked":
                reason = str(snapshot.get("blocked_reason") or "blocked")
                if last_mode != "blocked":
                    print(f"[{time.strftime('%H:%M:%S')}] blocked: {reason}")
                last_mode = "blocked"
                time.sleep(poll_seconds)
                continue

            if assignment is not None:
                checkbox = str(assignment.get("checkbox_ref") or "")
                if checkbox:
                    if last_mode != f"work:{checkbox}":
                        print(f"[{time.strftime('%H:%M:%S')}] executing {checkbox}")
                    last_mode = f"work:{checkbox}"
                    rc = subprocess.run(
                        [
                            str(root / "control-plane" / "worker-run-assignment.sh"),
                            "--agent",
                            agent_id,
                            "--checkbox",
                            checkbox,
                        ],
                        cwd=str(root),
                        check=False,
                    ).returncode
                    if rc == 0:
                        continue
                    if rc != 10:
                        db.block_agent(
                            agent_id,
                            f"worker_run_failed_rc_{rc}",
                            checkbox_ref=checkbox,
                        )
                    time.sleep(poll_seconds)
                    continue

            if last_mode != "idle":
                print(f"[{time.strftime('%H:%M:%S')}] standing_by")
            last_mode = "idle"
            time.sleep(poll_seconds)
    finally:
        try:
            final_state = db.mark_agent_stopped(agent_id, reason=stop_reason)
            print(
                f"agentd stopped: status={final_state.get('status')} checkbox={final_state.get('checkbox_ref')}"
            )
        finally:
            try:
                db.clear_agent_pid(agent_id)
            except Exception:
                pass
            if stop_path.exists():
                stop_path.unlink()
            if pid_path.exists():
                pid_path.unlink()
            fcntl.flock(lock_fd, fcntl.LOCK_UN)
            os.close(lock_fd)

    return 0


def _stop_agent(root: Path, agent_id: str) -> int:
    _lock_path, pid_path, stop_path = _state_paths(root, agent_id)
    stop_path.parent.mkdir(parents=True, exist_ok=True)
    stop_path.write_text("stop\n", encoding="utf-8")

    snapshot = db.get_agent_snapshot(agent_id)
    pid = snapshot.get("pid")
    if isinstance(pid, int) and pid > 0:
        try:
            os.kill(pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        except PermissionError:
            pass

    print(f"Stop requested for {agent_id}")
    return 0


def _unblock_agent(agent_id: str, reason: str) -> int:
    result = db.unblock_agent(agent_id, reason=reason)
    print(
        f"Unblocked {result.get('agent_id')}: status={result.get('status')} assignment={result.get('checkbox_ref')}"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="control-plane agent daemon")
    sub = parser.add_subparsers(dest="command", required=True)

    run_p = sub.add_parser("run", help="run worker daemon loop")
    run_p.add_argument("--agent", required=True)
    run_p.add_argument("--poll-seconds", type=int, default=5)
    run_p.add_argument("--lease-seconds", type=int, default=60)

    stop_p = sub.add_parser("stop", help="request graceful stop")
    stop_p.add_argument("--agent", required=True)

    unblock_p = sub.add_parser("unblock", help="clear blocked state")
    unblock_p.add_argument("--agent", required=True)
    unblock_p.add_argument("--reason", default="manual_unblock")

    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent

    if args.command == "run":
        return _run_loop(root, args.agent, args.poll_seconds, args.lease_seconds)
    if args.command == "stop":
        return _stop_agent(root, args.agent)
    if args.command == "unblock":
        return _unblock_agent(args.agent, args.reason)

    parser.print_help()
    return 2


if __name__ == "__main__":
    sys.exit(main())
