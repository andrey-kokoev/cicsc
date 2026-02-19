-- One-time migration for agentd protocol model.
-- Runtime also performs idempotent schema repair in control-plane/db.py.

PRAGMA foreign_keys = ON;

ALTER TABLE agents ADD COLUMN pid INTEGER;
ALTER TABLE agents ADD COLUMN heartbeat_at TEXT;
ALTER TABLE agents ADD COLUMN blocked_reason TEXT;
ALTER TABLE agents ADD COLUMN updated_at TEXT;

ALTER TABLE assignments ADD COLUMN lease_token TEXT;
ALTER TABLE assignments ADD COLUMN lease_expires_at TEXT;
ALTER TABLE assignments ADD COLUMN last_heartbeat_at TEXT;

ALTER TABLE events ADD COLUMN event_type TEXT;
ALTER TABLE events ADD COLUMN lease_token TEXT;

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
