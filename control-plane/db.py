#!/usr/bin/env python3
"""SQLite database access layer for control-plane"""

import sqlite3
import os
from pathlib import Path

DB_PATH = Path(__file__).parent.parent / "state" / "ledger.db"


def get_db():
    conn = sqlite3.connect(str(DB_PATH))
    conn.row_factory = sqlite3.Row
    return conn


def get_all_phases():
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM phases ORDER BY number")
    return [dict(row) for row in cur.fetchall()]


def get_phase(phase_id):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM phases WHERE id = ?", (phase_id,))
    row = cur.fetchone()
    conn.close()
    return dict(row) if row else None


def get_all_milestones():
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM milestones")
    return [dict(row) for row in cur.fetchall()]


def get_milestone(milestone_id):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM milestones WHERE id = ?", (milestone_id,))
    row = cur.fetchone()
    conn.close()
    return dict(row) if row else None


def get_milestones_by_phase(phase_id):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM milestones WHERE phase_id = ?", (phase_id,))
    return [dict(row) for row in cur.fetchall()]


def get_all_checkboxes():
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM checkboxes")
    return [dict(row) for row in cur.fetchall()]


def get_checkbox(checkbox_id):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM checkboxes WHERE id = ?", (checkbox_id,))
    row = cur.fetchone()
    conn.close()
    return dict(row) if row else None


def get_checkboxes_by_milestone(milestone_id):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM checkboxes WHERE milestone_id = ?", (milestone_id,))
    return [dict(row) for row in cur.fetchall()]


def update_checkbox_status(checkbox_id, status):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("UPDATE checkboxes SET status = ? WHERE id = ?", (status, checkbox_id))
    conn.commit()
    conn.close()


def get_all_assignments():
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM assignments")
    return [dict(row) for row in cur.fetchall()]


def get_assignment(checkbox_ref):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM assignments WHERE checkbox_ref = ?", (checkbox_ref,))
    row = cur.fetchone()
    conn.close()
    return dict(row) if row else None


def get_assignments_by_agent(agent_ref):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM assignments WHERE agent_ref = ?", (agent_ref,))
    return [dict(row) for row in cur.fetchall()]


def get_active_assignments():
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM assignments WHERE status = 'assigned'")
    rows = [dict(row) for row in cur.fetchall()]
    conn.close()
    return rows


def create_assignment(checkbox_ref, agent_ref, status="assigned"):
    conn = get_db()
    cur = conn.cursor()
    from datetime import datetime

    cur.execute(
        """
        INSERT INTO assignments (checkbox_ref, agent_ref, status, created_at)
        VALUES (?, ?, ?, ?)
    """,
        (checkbox_ref, agent_ref, status, datetime.now().isoformat() + "Z"),
    )
    conn.commit()
    conn.close()


def update_assignment(checkbox_ref, **kwargs):
    conn = get_db()
    cur = conn.cursor()
    set_clause = ", ".join(f"{k} = ?" for k in kwargs.keys())
    values = list(kwargs.values()) + [checkbox_ref]
    cur.execute(f"UPDATE assignments SET {set_clause} WHERE checkbox_ref = ?", values)
    conn.commit()
    conn.close()


def add_phase(id, number, status, title, description=""):
    conn = get_db()
    cur = conn.cursor()
    cur.execute(
        """
        INSERT INTO phases (id, number, status, title, description)
        VALUES (?, ?, ?, ?, ?)
    """,
        (id, number, status, title, description),
    )
    conn.commit()
    conn.close()


def add_milestone(id, phase_id, title):
    conn = get_db()
    cur = conn.cursor()
    cur.execute(
        """
        INSERT INTO milestones (id, phase_id, title)
        VALUES (?, ?, ?)
    """,
        (id, phase_id, title),
    )
    conn.commit()
    conn.close()


def add_checkbox(id, milestone_id, status="open", description=""):
    conn = get_db()
    cur = conn.cursor()
    cur.execute(
        """
        INSERT INTO checkboxes (id, milestone_id, status, description)
        VALUES (?, ?, ?, ?)
    """,
        (id, milestone_id, status, description),
    )
    conn.commit()
    conn.close()


def update_phase_status(phase_id, status):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("UPDATE phases SET status = ? WHERE id = ?", (status, phase_id))
    conn.commit()
    conn.close()


def get_phase_checkbox_stats(phase_id):
    conn = get_db()
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
    conn.close()
    return {"total": row[0], "done": row[1] or 0}


def get_or_create_agent(agent_id):
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM agents WHERE id = ?", (agent_id,))
    row = cur.fetchone()
    from datetime import datetime

    if not row:
        cur.execute(
            "INSERT INTO agents (id, standby_since, status) VALUES (?, ?, ?)",
            (agent_id, datetime.now().isoformat() + "Z", "standing_by"),
        )
        conn.commit()
        cur.execute("SELECT * FROM agents WHERE id = ?", (agent_id,))
        row = cur.fetchone()
    conn.close()
    return dict(row) if row else None


def agent_standby(agent_id):
    set_agent_status(agent_id, "standing_by")


def agent_busy(agent_id):
    set_agent_status(agent_id, "busy")


def set_agent_status(agent_id, status):
    from datetime import datetime

    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT status FROM agents WHERE id = ?", (agent_id,))
    row = cur.fetchone()
    now = datetime.now().isoformat() + "Z"

    if row is None:
        standby_since = now if status == "standing_by" else None
        cur.execute(
            "INSERT INTO agents (id, standby_since, status) VALUES (?, ?, ?)",
            (agent_id, standby_since, status),
        )
    elif row[0] != status:
        if status == "standing_by":
            cur.execute(
                "UPDATE agents SET status = ?, standby_since = ? WHERE id = ?",
                (status, now, agent_id),
            )
        else:
            cur.execute(
                "UPDATE agents SET status = ? WHERE id = ?",
                (status, agent_id),
            )
    conn.commit()
    conn.close()


def get_idle_agents():
    conn = get_db()
    cur = conn.cursor()
    cur.execute(
        "SELECT * FROM agents WHERE status = 'standing_by' ORDER BY standby_since ASC"
    )
    agents = [dict(row) for row in cur.fetchall()]
    conn.close()
    return agents


def get_agent_assignment(agent_id):
    conn = get_db()
    cur = conn.cursor()
    cur.execute(
        """
        SELECT a.*, c.description as task_description
        FROM assignments a
        JOIN checkboxes c ON a.checkbox_ref = c.id
        WHERE a.agent_ref = ? AND a.status = 'assigned'
    """,
        (agent_id,),
    )
    row = cur.fetchone()
    conn.close()
    return dict(row) if row else None


def assign_work_to_agent(checkbox_id, agent_id):
    from datetime import datetime

    conn = get_db()
    cur = conn.cursor()
    cur.execute(
        """
        INSERT OR REPLACE INTO assignments 
        (checkbox_ref, agent_ref, status, created_at)
        VALUES (?, ?, 'assigned', ?)
    """,
        (checkbox_id, agent_id, datetime.now().isoformat() + "Z"),
    )
    cur.execute("UPDATE agents SET status = 'busy' WHERE id = ?", (agent_id,))
    cur.execute(
        "UPDATE checkboxes SET status = 'open' WHERE id = ? AND status != 'done'",
        (checkbox_id,),
    )
    conn.commit()
    conn.close()


def complete_assignment(checkbox_id, commit_sha=None):
    from datetime import datetime

    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT status FROM assignments WHERE checkbox_ref = ?", (checkbox_id,))
    row = cur.fetchone()
    if row is None or row[0] != "assigned":
        conn.close()
        return False

    completed_at = datetime.now().isoformat() + "Z"
    if commit_sha:
        cur.execute(
            """
            UPDATE assignments
            SET status = 'done', commit_sha = ?, completed_at = ?
            WHERE checkbox_ref = ?
        """,
            (commit_sha, completed_at, checkbox_id),
        )
    else:
        cur.execute(
            """
            UPDATE assignments
            SET status = 'done', completed_at = ?
            WHERE checkbox_ref = ?
        """,
            (completed_at, checkbox_id),
        )
    cur.execute("UPDATE checkboxes SET status = 'done' WHERE id = ?", (checkbox_id,))
    conn.commit()
    conn.close()
    return True


def get_open_checkboxes():
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT * FROM checkboxes WHERE status = 'open' ORDER BY id")
    checkboxes = [dict(row) for row in cur.fetchall()]
    conn.close()
    return checkboxes


def get_assigned_checkboxes():
    conn = get_db()
    cur = conn.cursor()
    cur.execute("SELECT checkbox_ref FROM assignments WHERE status = 'assigned'")
    assigned = {row[0] for row in cur.fetchall()}
    conn.close()
    return assigned


if __name__ == "__main__":
    import json

    print(
        json.dumps(
            {
                "phases": get_all_phases(),
                "milestones": get_all_milestones(),
                "checkboxes": get_all_checkboxes(),
                "assignments": get_all_assignments(),
            },
            indent=2,
        )
    )
