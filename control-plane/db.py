#!/usr/bin/env python3
"""SQLite database access layer for control-plane."""

from __future__ import annotations

import json
import os
import sqlite3
import uuid
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any

DB_PATH = Path(
    os.environ.get(
        "CICSC_LEDGER_DB_PATH",
        str(Path(__file__).parent.parent / "state" / "ledger.db"),
    )
)

def _utcnow() -> datetime:
    return datetime.now(timezone.utc)


def _iso(dt: datetime | None = None) -> str:
    current = dt or _utcnow()
    return current.isoformat().replace("+00:00", "Z")


def _parse_iso(value: str | None) -> datetime | None:
    if not value:
        return None
    try:
        parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
        if parsed.tzinfo is None:
            parsed = parsed.replace(tzinfo=timezone.utc)
        return parsed.astimezone(timezone.utc)
    except ValueError:
        return None


def _add_seconds(value: str | None, seconds: int) -> str:
    base = _parse_iso(value) or _utcnow()
    return _iso(base + timedelta(seconds=seconds))


def _seconds_since(value: str | None) -> int | None:
    parsed = _parse_iso(value)
    if parsed is None:
        return None
    delta = _utcnow() - parsed
    return max(0, int(delta.total_seconds()))


def _event_details_text(details: str | dict[str, Any] | None) -> str | None:
    if details is None:
        return None
    if isinstance(details, str):
        return details
    return json.dumps(details, sort_keys=True)


def _table_columns(conn: sqlite3.Connection, table: str) -> set[str]:
    cur = conn.cursor()
    cur.execute(f"PRAGMA table_info({table})")
    return {str(row[1]) for row in cur.fetchall()}


def _add_column_if_missing(conn: sqlite3.Connection, table: str, column: str, decl: str) -> None:
    cols = _table_columns(conn, table)
    if column not in cols:
        conn.execute(f"ALTER TABLE {table} ADD COLUMN {column} {decl}")


def ensure_schema(conn: sqlite3.Connection) -> None:
    conn.execute("PRAGMA foreign_keys = ON")
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS phases (
            id TEXT PRIMARY KEY,
            number INTEGER,
            status TEXT CHECK(status IN ('planned','in_progress','complete','deferred')),
            title TEXT,
            description TEXT
        );

        CREATE TABLE IF NOT EXISTS milestones (
            id TEXT PRIMARY KEY,
            phase_id TEXT REFERENCES phases(id),
            title TEXT
        );

        CREATE TABLE IF NOT EXISTS checkboxes (
            id TEXT PRIMARY KEY,
            milestone_id TEXT REFERENCES milestones(id),
            status TEXT CHECK(status IN ('open','done')),
            description TEXT
        );

        CREATE TABLE IF NOT EXISTS assignments (
            checkbox_ref TEXT PRIMARY KEY REFERENCES checkboxes(id),
            agent_ref TEXT REFERENCES agents(id),
            status TEXT CHECK(status IN ('assigned','done')),
            created_at TEXT,
            started_at TEXT,
            commit_sha TEXT,
            completed_at TEXT,
            lease_token TEXT,
            lease_expires_at TEXT,
            last_heartbeat_at TEXT
        );

        CREATE TABLE IF NOT EXISTS agents (
            id TEXT PRIMARY KEY,
            standby_since TEXT,
            status TEXT CHECK(status IN ('standing_by','busy','blocked')),
            pid INTEGER,
            heartbeat_at TEXT,
            blocked_reason TEXT,
            updated_at TEXT
        );

        CREATE TABLE IF NOT EXISTS events (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            event_type TEXT,
            type TEXT,
            checkbox_ref TEXT,
            agent_ref TEXT,
            lease_token TEXT,
            timestamp TEXT,
            details TEXT
        );
        """
    )

    _add_column_if_missing(conn, "agents", "pid", "INTEGER")
    _add_column_if_missing(conn, "agents", "heartbeat_at", "TEXT")
    _add_column_if_missing(conn, "agents", "blocked_reason", "TEXT")
    _add_column_if_missing(conn, "agents", "updated_at", "TEXT")

    _add_column_if_missing(conn, "assignments", "lease_token", "TEXT")
    _add_column_if_missing(conn, "assignments", "lease_expires_at", "TEXT")
    _add_column_if_missing(conn, "assignments", "last_heartbeat_at", "TEXT")

    _add_column_if_missing(conn, "events", "event_type", "TEXT")
    _add_column_if_missing(conn, "events", "lease_token", "TEXT")

    conn.executescript(
        """
        CREATE INDEX IF NOT EXISTS idx_assignments_agent_status
          ON assignments(agent_ref, status);
        CREATE INDEX IF NOT EXISTS idx_assignments_status_lease
          ON assignments(status, lease_expires_at);
        CREATE INDEX IF NOT EXISTS idx_agents_status_heartbeat
          ON agents(status, heartbeat_at);
        CREATE INDEX IF NOT EXISTS idx_events_agent_ts
          ON events(agent_ref, timestamp);
        CREATE INDEX IF NOT EXISTS idx_events_checkbox_ts
          ON events(checkbox_ref, timestamp);

        CREATE TRIGGER IF NOT EXISTS trg_agents_standing_by_requires_no_assignment
        BEFORE UPDATE OF status ON agents
        WHEN NEW.status = 'standing_by'
          AND EXISTS (
            SELECT 1 FROM assignments a
            WHERE a.agent_ref = NEW.id AND a.status = 'assigned'
          )
        BEGIN
          SELECT RAISE(ABORT, 'agent cannot be standing_by with active assignment');
        END;

        CREATE TRIGGER IF NOT EXISTS trg_assignments_no_done_to_assigned
        BEFORE UPDATE ON assignments
        WHEN OLD.status = 'done' AND NEW.status = 'assigned'
        BEGIN
          SELECT RAISE(ABORT, 'assignment status regression done->assigned is forbidden');
        END;

        CREATE TRIGGER IF NOT EXISTS trg_assignments_done_requires_commit
        BEFORE UPDATE ON assignments
        WHEN OLD.status = 'assigned' AND NEW.status = 'done'
          AND (NEW.commit_sha IS NULL OR TRIM(NEW.commit_sha) = '')
        BEGIN
          SELECT RAISE(ABORT, 'assignment completion requires commit_sha');
        END;

        CREATE TRIGGER IF NOT EXISTS trg_assignments_insert_requires_standing_by
        BEFORE INSERT ON assignments
        WHEN NEW.status = 'assigned'
          AND COALESCE((SELECT status FROM agents WHERE id = NEW.agent_ref), '') != 'standing_by'
        BEGIN
          SELECT RAISE(ABORT, 'assigned work requires standing_by agent');
        END;

        CREATE TRIGGER IF NOT EXISTS trg_assignments_update_requires_standing_by
        BEFORE UPDATE OF status, agent_ref ON assignments
        WHEN NEW.status = 'assigned'
          AND COALESCE((SELECT status FROM agents WHERE id = NEW.agent_ref), '') != 'standing_by'
          AND NOT (OLD.status = 'assigned' AND OLD.agent_ref = NEW.agent_ref)
        BEGIN
          SELECT RAISE(ABORT, 'assigned work requires standing_by agent');
        END;
        """
    )

    now = _iso()
    conn.execute(
        "UPDATE agents SET updated_at = COALESCE(updated_at, ?) WHERE updated_at IS NULL",
        (now,),
    )
    conn.execute(
        "UPDATE agents SET heartbeat_at = COALESCE(heartbeat_at, updated_at) WHERE heartbeat_at IS NULL"
    )
    conn.execute(
        "UPDATE events SET event_type = COALESCE(event_type, type) WHERE event_type IS NULL"
    )
    conn.execute(
        """
        UPDATE assignments
        SET lease_token = COALESCE(NULLIF(TRIM(lease_token), ''), LOWER(HEX(RANDOMBLOB(16))))
        WHERE status = 'assigned'
        """
    )
    conn.execute(
        "UPDATE assignments SET lease_expires_at = COALESCE(lease_expires_at, ?) WHERE status = 'assigned'",
        (_add_seconds(now, 60),),
    )
    conn.execute(
        "UPDATE assignments SET last_heartbeat_at = COALESCE(last_heartbeat_at, ?) WHERE status = 'assigned'",
        (now,),
    )
    conn.execute(
        """
        UPDATE assignments
        SET commit_sha = COALESCE(NULLIF(TRIM(commit_sha), ''), 'legacy-pre-agentd')
        WHERE status = 'done'
        """
    )
    conn.execute(
        "UPDATE assignments SET completed_at = COALESCE(completed_at, created_at, ?) WHERE status = 'done'",
        (now,),
    )
    conn.commit()


def get_db() -> sqlite3.Connection:
    conn = sqlite3.connect(str(DB_PATH))
    conn.row_factory = sqlite3.Row
    ensure_schema(conn)
    return conn


def _fetchall(query: str, args: tuple[Any, ...] = ()) -> list[dict[str, Any]]:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute(query, args)
        return [dict(row) for row in cur.fetchall()]
    finally:
        conn.close()


def _fetchone(query: str, args: tuple[Any, ...] = ()) -> dict[str, Any] | None:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute(query, args)
        row = cur.fetchone()
        return dict(row) if row else None
    finally:
        conn.close()


def _append_event_cur(
    cur: sqlite3.Cursor,
    event_type: str,
    checkbox_ref: str | None = None,
    agent_ref: str | None = None,
    lease_token: str | None = None,
    details: str | dict[str, Any] | None = None,
) -> None:
    ts = _iso()
    detail_text = _event_details_text(details)
    cur.execute(
        """
        INSERT INTO events (event_type, type, checkbox_ref, agent_ref, lease_token, timestamp, details)
        VALUES (?, ?, ?, ?, ?, ?, ?)
        """,
        (event_type, event_type, checkbox_ref, agent_ref, lease_token, ts, detail_text),
    )


def append_event(
    event_type: str,
    checkbox_ref: str | None = None,
    agent_ref: str | None = None,
    lease_token: str | None = None,
    details: str | dict[str, Any] | None = None,
) -> None:
    conn = get_db()
    try:
        cur = conn.cursor()
        _append_event_cur(cur, event_type, checkbox_ref, agent_ref, lease_token, details)
        conn.commit()
    finally:
        conn.close()


def get_all_phases() -> list[dict[str, Any]]:
    return _fetchall("SELECT * FROM phases ORDER BY number")


def get_phase(phase_id: str) -> dict[str, Any] | None:
    return _fetchone("SELECT * FROM phases WHERE id = ?", (phase_id,))


def get_all_milestones() -> list[dict[str, Any]]:
    return _fetchall("SELECT * FROM milestones")


def get_milestone(milestone_id: str) -> dict[str, Any] | None:
    return _fetchone("SELECT * FROM milestones WHERE id = ?", (milestone_id,))


def get_milestones_by_phase(phase_id: str) -> list[dict[str, Any]]:
    return _fetchall("SELECT * FROM milestones WHERE phase_id = ?", (phase_id,))


def get_all_checkboxes() -> list[dict[str, Any]]:
    return _fetchall("SELECT * FROM checkboxes")


def get_checkbox(checkbox_id: str) -> dict[str, Any] | None:
    return _fetchone("SELECT * FROM checkboxes WHERE id = ?", (checkbox_id,))


def get_checkboxes_by_milestone(milestone_id: str) -> list[dict[str, Any]]:
    return _fetchall("SELECT * FROM checkboxes WHERE milestone_id = ?", (milestone_id,))


def update_checkbox_status(checkbox_id: str, status: str) -> None:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute("UPDATE checkboxes SET status = ? WHERE id = ?", (status, checkbox_id))
        conn.commit()
    finally:
        conn.close()


def get_all_assignments() -> list[dict[str, Any]]:
    return _fetchall("SELECT * FROM assignments")


def get_assignment(checkbox_ref: str) -> dict[str, Any] | None:
    return _fetchone("SELECT * FROM assignments WHERE checkbox_ref = ?", (checkbox_ref,))


def get_assignments_by_agent(agent_ref: str) -> list[dict[str, Any]]:
    return _fetchall("SELECT * FROM assignments WHERE agent_ref = ?", (agent_ref,))


def get_active_assignments() -> list[dict[str, Any]]:
    return _fetchall("SELECT * FROM assignments WHERE status = 'assigned'")


def add_phase(id: str, number: int, status: str, title: str, description: str = "") -> None:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute(
            """
            INSERT INTO phases (id, number, status, title, description)
            VALUES (?, ?, ?, ?, ?)
            """,
            (id, number, status, title, description),
        )
        conn.commit()
    finally:
        conn.close()


def add_milestone(id: str, phase_id: str, title: str) -> None:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute(
            """
            INSERT INTO milestones (id, phase_id, title)
            VALUES (?, ?, ?)
            """,
            (id, phase_id, title),
        )
        conn.commit()
    finally:
        conn.close()


def add_checkbox(id: str, milestone_id: str, status: str = "open", description: str = "") -> None:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute(
            """
            INSERT INTO checkboxes (id, milestone_id, status, description)
            VALUES (?, ?, ?, ?)
            """,
            (id, milestone_id, status, description),
        )
        conn.commit()
    finally:
        conn.close()


def update_phase_status(phase_id: str, status: str) -> None:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute("UPDATE phases SET status = ? WHERE id = ?", (status, phase_id))
        conn.commit()
    finally:
        conn.close()


def get_phase_checkbox_stats(phase_id: str) -> dict[str, int]:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute(
            """
            SELECT COUNT(*) as total,
                   SUM(CASE WHEN c.status = 'done' THEN 1 ELSE 0 END) as done
            FROM checkboxes c
            JOIN milestones m ON c.milestone_id = m.id
            WHERE m.phase_id = ?
            """,
            (phase_id,),
        )
        row = cur.fetchone()
        return {"total": int(row[0]), "done": int(row[1] or 0)}
    finally:
        conn.close()


def get_or_create_agent(agent_id: str) -> dict[str, Any] | None:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute("SELECT * FROM agents WHERE id = ?", (agent_id,))
        row = cur.fetchone()
        now = _iso()
        if not row:
            cur.execute(
                """
                INSERT INTO agents (id, standby_since, status, heartbeat_at, updated_at)
                VALUES (?, ?, 'standing_by', ?, ?)
                """,
                (agent_id, now, now, now),
            )
            conn.commit()
            cur.execute("SELECT * FROM agents WHERE id = ?", (agent_id,))
            row = cur.fetchone()
        return dict(row) if row else None
    finally:
        conn.close()


def clear_agent_pid(agent_id: str) -> None:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute(
            "UPDATE agents SET pid = NULL, updated_at = ? WHERE id = ?",
            (_iso(), agent_id),
        )
        conn.commit()
    finally:
        conn.close()


def heartbeat_agent(agent_id: str, pid: int | None = None, lease_seconds: int = 60) -> dict[str, Any] | None:
    conn = get_db()
    try:
        cur = conn.cursor()
        now = _iso()
        lease_until = _add_seconds(now, lease_seconds)

        cur.execute("SELECT * FROM agents WHERE id = ?", (agent_id,))
        row = cur.fetchone()
        if row is None:
            cur.execute(
                """
                INSERT INTO agents (id, standby_since, status, pid, heartbeat_at, updated_at)
                VALUES (?, ?, 'standing_by', ?, ?, ?)
                """,
                (agent_id, now, pid, now, now),
            )
            status = "standing_by"
        else:
            status = str(row["status"])
            if pid is None:
                cur.execute(
                    "UPDATE agents SET heartbeat_at = ?, updated_at = ? WHERE id = ?",
                    (now, now, agent_id),
                )
            else:
                cur.execute(
                    "UPDATE agents SET pid = ?, heartbeat_at = ?, updated_at = ? WHERE id = ?",
                    (pid, now, now, agent_id),
                )

        cur.execute(
            """
            SELECT a.*, c.description as task_description
            FROM assignments a
            JOIN checkboxes c ON c.id = a.checkbox_ref
            WHERE a.agent_ref = ? AND a.status = 'assigned'
            ORDER BY a.created_at ASC
            LIMIT 1
            """,
            (agent_id,),
        )
        assignment = cur.fetchone()

        if assignment is not None:
            cur.execute(
                """
                UPDATE assignments
                SET last_heartbeat_at = ?, lease_expires_at = ?
                WHERE checkbox_ref = ? AND status = 'assigned'
                """,
                (now, lease_until, assignment["checkbox_ref"]),
            )
            if status != "blocked":
                cur.execute(
                    "UPDATE agents SET status = 'busy', updated_at = ? WHERE id = ?",
                    (now, agent_id),
                )
        else:
            if status != "blocked":
                cur.execute(
                    """
                    UPDATE agents
                    SET status = 'standing_by', standby_since = ?, updated_at = ?
                    WHERE id = ?
                    """,
                    (now, now, agent_id),
                )

        conn.commit()
        return dict(assignment) if assignment else None
    finally:
        conn.close()


def block_agent(agent_id: str, reason: str, checkbox_ref: str | None = None) -> None:
    conn = get_db()
    try:
        cur = conn.cursor()
        now = _iso()
        cur.execute("SELECT id FROM agents WHERE id = ?", (agent_id,))
        if cur.fetchone() is None:
            cur.execute(
                """
                INSERT INTO agents (id, status, blocked_reason, heartbeat_at, updated_at)
                VALUES (?, 'blocked', ?, ?, ?)
                """,
                (agent_id, reason, now, now),
            )
        else:
            cur.execute(
                """
                UPDATE agents
                SET status = 'blocked', blocked_reason = ?, heartbeat_at = ?, updated_at = ?
                WHERE id = ?
                """,
                (reason, now, now, agent_id),
            )
        _append_event_cur(
            cur,
            "blocked",
            checkbox_ref=checkbox_ref,
            agent_ref=agent_id,
            details={"reason": reason},
        )
        conn.commit()
    finally:
        conn.close()


def unblock_agent(agent_id: str, reason: str | None = None) -> dict[str, Any]:
    conn = get_db()
    try:
        cur = conn.cursor()
        now = _iso()

        cur.execute(
            "SELECT checkbox_ref FROM assignments WHERE agent_ref = ? AND status = 'assigned' LIMIT 1",
            (agent_id,),
        )
        assigned = cur.fetchone()
        next_status = "busy" if assigned else "standing_by"

        cur.execute(
            """
            UPDATE agents
            SET status = ?, blocked_reason = NULL, standby_since = CASE WHEN ? = 'standing_by' THEN ? ELSE standby_since END,
                heartbeat_at = ?, updated_at = ?
            WHERE id = ?
            """,
            (next_status, next_status, now, now, now, agent_id),
        )
        _append_event_cur(
            cur,
            "unblocked",
            checkbox_ref=(assigned["checkbox_ref"] if assigned else None),
            agent_ref=agent_id,
            details={"reason": reason or ""},
        )
        conn.commit()
        return {
            "agent_id": agent_id,
            "status": next_status,
            "checkbox_ref": assigned["checkbox_ref"] if assigned else None,
        }
    finally:
        conn.close()


def mark_agent_stopped(agent_id: str, reason: str = "stopped_by_operator") -> dict[str, Any]:
    conn = get_db()
    try:
        cur = conn.cursor()
        now = _iso()
        cur.execute(
            "SELECT checkbox_ref FROM assignments WHERE agent_ref = ? AND status = 'assigned' LIMIT 1",
            (agent_id,),
        )
        assigned = cur.fetchone()

        if assigned:
            cur.execute(
                """
                UPDATE agents
                SET status = 'blocked', blocked_reason = ?, pid = NULL, heartbeat_at = ?, updated_at = ?
                WHERE id = ?
                """,
                (reason, now, now, agent_id),
            )
            resulting_status = "blocked"
            checkbox_ref = assigned["checkbox_ref"]
        else:
            cur.execute(
                """
                UPDATE agents
                SET status = 'standing_by', blocked_reason = NULL, pid = NULL,
                    standby_since = ?, heartbeat_at = ?, updated_at = ?
                WHERE id = ?
                """,
                (now, now, now, agent_id),
            )
            resulting_status = "standing_by"
            checkbox_ref = None

        _append_event_cur(
            cur,
            "agent_stopped",
            checkbox_ref=checkbox_ref,
            agent_ref=agent_id,
            details={"reason": reason},
        )
        conn.commit()
        return {
            "agent_id": agent_id,
            "status": resulting_status,
            "checkbox_ref": checkbox_ref,
        }
    finally:
        conn.close()


def get_idle_agents() -> list[dict[str, Any]]:
    return _fetchall("SELECT * FROM agents WHERE status = 'standing_by' ORDER BY standby_since ASC")


def get_assignable_agents(max_heartbeat_age_seconds: int = 30) -> list[dict[str, Any]]:
    candidates = _fetchall(
        "SELECT * FROM agents WHERE status = 'standing_by' ORDER BY standby_since ASC"
    )
    assignable: list[dict[str, Any]] = []
    for agent in candidates:
        age = _seconds_since(str(agent.get("heartbeat_at") or ""))
        if age is None:
            continue
        if age <= max_heartbeat_age_seconds:
            assignable.append(agent)
    return assignable


def get_agent_assignment(agent_id: str) -> dict[str, Any] | None:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute(
            """
            SELECT a.*, c.description as task_description
            FROM assignments a
            JOIN checkboxes c ON a.checkbox_ref = c.id
            WHERE a.agent_ref = ? AND a.status = 'assigned'
            ORDER BY a.created_at ASC
            LIMIT 1
            """,
            (agent_id,),
        )
        row = cur.fetchone()
        return dict(row) if row else None
    finally:
        conn.close()


def claim_assignment(checkbox_id: str, agent_id: str, lease_seconds: int = 60) -> dict[str, Any] | None:
    conn = get_db()
    try:
        cur = conn.cursor()
        conn.execute("BEGIN IMMEDIATE")

        cur.execute("SELECT status FROM checkboxes WHERE id = ?", (checkbox_id,))
        cb = cur.fetchone()
        if cb is None or cb[0] != "open":
            conn.rollback()
            return None

        cur.execute("SELECT status FROM assignments WHERE checkbox_ref = ?", (checkbox_id,))
        existing = cur.fetchone()
        if existing is not None:
            conn.rollback()
            return None

        cur.execute("SELECT status FROM agents WHERE id = ?", (agent_id,))
        agent = cur.fetchone()
        if agent is None or agent[0] != "standing_by":
            conn.rollback()
            return None

        now = _iso()
        lease_token = str(uuid.uuid4())
        lease_expires_at = _add_seconds(now, lease_seconds)

        cur.execute(
            """
            INSERT INTO assignments
            (checkbox_ref, agent_ref, status, created_at, started_at, lease_token, lease_expires_at, last_heartbeat_at)
            VALUES (?, ?, 'assigned', ?, ?, ?, ?, ?)
            """,
            (checkbox_id, agent_id, now, now, lease_token, lease_expires_at, now),
        )
        cur.execute(
            """
            UPDATE agents
            SET status = 'busy', blocked_reason = NULL, updated_at = ?, heartbeat_at = ?
            WHERE id = ?
            """,
            (now, now, agent_id),
        )
        _append_event_cur(
            cur,
            "assigned",
            checkbox_ref=checkbox_id,
            agent_ref=agent_id,
            lease_token=lease_token,
            details={"lease_expires_at": lease_expires_at},
        )
        conn.commit()
        return {
            "checkbox_ref": checkbox_id,
            "agent_ref": agent_id,
            "lease_token": lease_token,
            "lease_expires_at": lease_expires_at,
        }
    except sqlite3.IntegrityError:
        conn.rollback()
        return None
    finally:
        conn.close()


def assign_work_to_agent(checkbox_id: str, agent_id: str, lease_seconds: int = 60) -> bool:
    return claim_assignment(checkbox_id, agent_id, lease_seconds=lease_seconds) is not None


def touch_assignment_lease(agent_id: str, checkbox_id: str, lease_seconds: int = 60) -> bool:
    conn = get_db()
    try:
        cur = conn.cursor()
        now = _iso()
        lease_expires = _add_seconds(now, lease_seconds)
        cur.execute(
            """
            UPDATE assignments
            SET last_heartbeat_at = ?, lease_expires_at = ?
            WHERE checkbox_ref = ? AND agent_ref = ? AND status = 'assigned'
            """,
            (now, lease_expires, checkbox_id, agent_id),
        )
        changed = cur.rowcount > 0
        if changed:
            cur.execute(
                "UPDATE agents SET heartbeat_at = ?, updated_at = ? WHERE id = ?",
                (now, now, agent_id),
            )
        conn.commit()
        return changed
    finally:
        conn.close()


def reclaim_stale_assignments(heartbeat_grace_seconds: int = 30) -> list[dict[str, Any]]:
    conn = get_db()
    reclaimed: list[dict[str, Any]] = []
    try:
        cur = conn.cursor()
        conn.execute("BEGIN IMMEDIATE")
        now = _utcnow()

        cur.execute(
            """
            SELECT a.checkbox_ref, a.agent_ref, a.lease_token, a.lease_expires_at,
                   a.last_heartbeat_at, ag.status AS agent_status, ag.blocked_reason
            FROM assignments a
            JOIN agents ag ON ag.id = a.agent_ref
            WHERE a.status = 'assigned'
            """
        )
        rows = cur.fetchall()

        for row in rows:
            agent_status = str(row["agent_status"] or "")
            if agent_status == "blocked":
                continue

            lease_expires = _parse_iso(str(row["lease_expires_at"] or ""))
            if lease_expires is None or now <= lease_expires:
                continue

            last_hb = _parse_iso(str(row["last_heartbeat_at"] or ""))
            hb_stale = True
            if last_hb is not None:
                hb_stale = (now - last_hb).total_seconds() > heartbeat_grace_seconds
            if not hb_stale:
                continue

            checkbox_ref = str(row["checkbox_ref"])
            agent_ref = str(row["agent_ref"])
            lease_token = str(row["lease_token"] or "")

            cur.execute(
                "DELETE FROM assignments WHERE checkbox_ref = ? AND status = 'assigned'",
                (checkbox_ref,),
            )
            cur.execute(
                "UPDATE checkboxes SET status = 'open' WHERE id = ? AND status != 'done'",
                (checkbox_ref,),
            )
            cur.execute(
                "SELECT COUNT(*) FROM assignments WHERE agent_ref = ? AND status = 'assigned'",
                (agent_ref,),
            )
            remaining = int(cur.fetchone()[0])
            if remaining == 0:
                cur.execute(
                    """
                    UPDATE agents
                    SET status = 'standing_by', standby_since = ?, updated_at = ?, blocked_reason = NULL
                    WHERE id = ? AND status != 'blocked'
                    """,
                    (_iso(now), _iso(now), agent_ref),
                )

            _append_event_cur(
                cur,
                "assignment_reclaimed",
                checkbox_ref=checkbox_ref,
                agent_ref=agent_ref,
                lease_token=lease_token or None,
                details={
                    "reason": "lease_expired_and_heartbeat_stale",
                    "heartbeat_grace_seconds": heartbeat_grace_seconds,
                },
            )
            reclaimed.append(
                {
                    "checkbox_ref": checkbox_ref,
                    "agent_ref": agent_ref,
                    "lease_token": lease_token,
                }
            )

        conn.commit()
        return reclaimed
    finally:
        conn.close()


def complete_assignment(
    checkbox_id: str,
    commit_sha: str | None,
    expected_agent: str,
) -> bool:
    if not commit_sha or not str(commit_sha).strip():
        return False
    if not expected_agent or not str(expected_agent).strip():
        return False

    conn = get_db()
    try:
        cur = conn.cursor()
        conn.execute("BEGIN IMMEDIATE")

        cur.execute(
            "SELECT checkbox_ref, agent_ref, status, lease_token FROM assignments WHERE checkbox_ref = ?",
            (checkbox_id,),
        )
        row = cur.fetchone()
        if row is None or row["status"] != "assigned":
            conn.rollback()
            return False

        if row["agent_ref"] != expected_agent:
            conn.rollback()
            return False

        completed_at = _iso()
        cur.execute(
            """
            UPDATE assignments
            SET status = 'done', commit_sha = ?, completed_at = ?,
                lease_token = NULL, lease_expires_at = NULL, last_heartbeat_at = ?
            WHERE checkbox_ref = ?
            """,
            (commit_sha, completed_at, completed_at, checkbox_id),
        )
        cur.execute("UPDATE checkboxes SET status = 'done' WHERE id = ?", (checkbox_id,))

        agent_ref = str(row["agent_ref"])
        cur.execute(
            "SELECT status FROM agents WHERE id = ?",
            (agent_ref,),
        )
        agent_row = cur.fetchone()
        if agent_row is not None and agent_row[0] != "blocked":
            cur.execute(
                "SELECT COUNT(*) FROM assignments WHERE agent_ref = ? AND status = 'assigned'",
                (agent_ref,),
            )
            remaining = int(cur.fetchone()[0])
            if remaining == 0:
                cur.execute(
                    """
                    UPDATE agents
                    SET status = 'standing_by', standby_since = ?, updated_at = ?, blocked_reason = NULL
                    WHERE id = ?
                    """,
                    (completed_at, completed_at, agent_ref),
                )

        _append_event_cur(
            cur,
            "integrated",
            checkbox_ref=checkbox_id,
            agent_ref=agent_ref,
            details={"commit_sha": commit_sha},
        )

        conn.commit()
        return True
    except sqlite3.IntegrityError:
        conn.rollback()
        return False
    finally:
        conn.close()


def get_open_checkboxes() -> list[dict[str, Any]]:
    return _fetchall("SELECT * FROM checkboxes WHERE status = 'open' ORDER BY id")


def get_assigned_checkboxes() -> set[str]:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute("SELECT checkbox_ref FROM assignments WHERE status = 'assigned'")
        return {str(row[0]) for row in cur.fetchall()}
    finally:
        conn.close()


def get_latest_event(agent_id: str | None = None, checkbox_ref: str | None = None) -> dict[str, Any] | None:
    conn = get_db()
    try:
        cur = conn.cursor()
        if agent_id is not None:
            cur.execute(
                "SELECT * FROM events WHERE agent_ref = ? ORDER BY id DESC LIMIT 1",
                (agent_id,),
            )
        elif checkbox_ref is not None:
            cur.execute(
                "SELECT * FROM events WHERE checkbox_ref = ? ORDER BY id DESC LIMIT 1",
                (checkbox_ref,),
            )
        else:
            cur.execute("SELECT * FROM events ORDER BY id DESC LIMIT 1")
        row = cur.fetchone()
        return dict(row) if row else None
    finally:
        conn.close()


def get_agent_snapshot(agent_id: str) -> dict[str, Any]:
    conn = get_db()
    try:
        cur = conn.cursor()
        cur.execute("SELECT * FROM agents WHERE id = ?", (agent_id,))
        agent = cur.fetchone()
        cur.execute(
            """
            SELECT a.*, c.description AS task_description
            FROM assignments a
            JOIN checkboxes c ON c.id = a.checkbox_ref
            WHERE a.agent_ref = ? AND a.status = 'assigned'
            ORDER BY a.created_at ASC
            LIMIT 1
            """,
            (agent_id,),
        )
        assignment = cur.fetchone()

        cur.execute(
            "SELECT * FROM events WHERE agent_ref = ? ORDER BY id DESC LIMIT 1",
            (agent_id,),
        )
        last_event = cur.fetchone()

        if agent is None:
            return {
                "agent_id": agent_id,
                "exists": False,
                "status": "unknown",
                "assignment": None,
                "heartbeat_age_seconds": None,
                "lease_age_seconds": None,
                "pid": None,
                "blocked_reason": None,
                "last_event": dict(last_event) if last_event else None,
            }

        agent_d = dict(agent)
        assignment_d = dict(assignment) if assignment else None

        return {
            "agent_id": agent_id,
            "exists": True,
            "status": agent_d.get("status"),
            "assignment": assignment_d,
            "heartbeat_age_seconds": _seconds_since(str(agent_d.get("heartbeat_at") or "")),
            "lease_age_seconds": (
                _seconds_since(str(assignment_d.get("last_heartbeat_at") or ""))
                if assignment_d
                else None
            ),
            "lease_expires_in_seconds": (
                (
                    int(((_parse_iso(str(assignment_d.get("lease_expires_at") or "")) or _utcnow()) - _utcnow()).total_seconds())
                )
                if assignment_d and assignment_d.get("lease_expires_at")
                else None
            ),
            "pid": agent_d.get("pid"),
            "blocked_reason": agent_d.get("blocked_reason"),
            "last_event": dict(last_event) if last_event else None,
        }
    finally:
        conn.close()


def list_agent_snapshots() -> list[dict[str, Any]]:
    agents = _fetchall("SELECT id FROM agents ORDER BY id ASC")
    return [get_agent_snapshot(str(agent["id"])) for agent in agents]


def get_collab_summary(max_heartbeat_age_seconds: int = 30) -> dict[str, Any]:
    conn = get_db()
    try:
        cur = conn.cursor()
        now = _utcnow()

        cur.execute(
            """
            SELECT
              SUM(CASE WHEN status = 'standing_by' THEN 1 ELSE 0 END) AS standing_by,
              SUM(CASE WHEN status = 'busy' THEN 1 ELSE 0 END) AS busy,
              SUM(CASE WHEN status = 'blocked' THEN 1 ELSE 0 END) AS blocked,
              COUNT(*) AS total_agents
            FROM agents
            """
        )
        agent_counts = dict(cur.fetchone() or {})
        cur.execute("SELECT id, status, heartbeat_at FROM agents")
        assignable_idle_count = 0
        for row in cur.fetchall():
            if str(row["status"] or "") != "standing_by":
                continue
            age = _seconds_since(str(row["heartbeat_at"] or ""))
            if age is not None and age <= max_heartbeat_age_seconds:
                assignable_idle_count += 1

        cur.execute("SELECT COUNT(*) FROM assignments WHERE status = 'assigned'")
        assigned_count = int(cur.fetchone()[0])

        cur.execute("SELECT COUNT(*) FROM checkboxes WHERE status = 'open'")
        open_count = int(cur.fetchone()[0])

        cur.execute(
            """
            SELECT COUNT(*)
            FROM checkboxes c
            LEFT JOIN assignments a
              ON a.checkbox_ref = c.id AND a.status = 'assigned'
            WHERE c.status = 'open' AND a.checkbox_ref IS NULL
            """
        )
        unassigned_open_count = int(cur.fetchone()[0])

        cur.execute(
            """
            SELECT a.lease_expires_at, ag.status
            FROM assignments a
            JOIN agents ag ON ag.id = a.agent_ref
            WHERE a.status = 'assigned'
            """
        )
        stale_lease_count = 0
        for row in cur.fetchall():
            if str(row["status"] or "") == "blocked":
                continue
            expires_at = _parse_iso(str(row["lease_expires_at"] or ""))
            if expires_at is None:
                continue
            if now > expires_at:
                stale_lease_count += 1

        return {
            "generated_at": _iso(now),
            "total_agents": int(agent_counts.get("total_agents") or 0),
            "standing_by": int(agent_counts.get("standing_by") or 0),
            "busy": int(agent_counts.get("busy") or 0),
            "blocked": int(agent_counts.get("blocked") or 0),
            "assignable_idle_count": assignable_idle_count,
            "assigned_count": assigned_count,
            "open_count": open_count,
            "unassigned_open_count": unassigned_open_count,
            "stale_lease_count": stale_lease_count,
        }
    finally:
        conn.close()


if __name__ == "__main__":
    print(
        json.dumps(
            {
                "phases": get_all_phases(),
                "milestones": get_all_milestones(),
                "checkboxes": get_all_checkboxes(),
                "assignments": get_all_assignments(),
                "agents": _fetchall("SELECT * FROM agents ORDER BY id"),
            },
            indent=2,
        )
    )
