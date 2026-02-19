import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import os from "node:os"
import path from "node:path"
import { spawnSync } from "node:child_process"

const ROOT = process.cwd()

function runPy(dbPath: string, py: string): string {
  const run = spawnSync("python3", ["-c", py], {
    cwd: ROOT,
    env: {
      ...process.env,
      CICSC_LEDGER_DB_PATH: dbPath,
    },
    encoding: "utf8",
  })
  assert.equal(run.status, 0, run.stderr || run.stdout)
  return run.stdout
}

function seedStatusFixture(dbPath: string): void {
  runPy(
    dbPath,
    `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute("INSERT INTO phases (id, number, status, title, description) VALUES ('S', 1, 'in_progress', 'Status', '')")
cur.execute("INSERT INTO milestones (id, phase_id, title) VALUES ('S1', 'S', 'M')")
cur.execute("INSERT INTO checkboxes (id, milestone_id, status, description) VALUES ('S1.1', 'S1', 'open', 'assigned open')")
cur.execute("INSERT INTO checkboxes (id, milestone_id, status, description) VALUES ('S1.2', 'S1', 'open', 'unassigned open')")
cur.execute("INSERT INTO checkboxes (id, milestone_id, status, description) VALUES ('S1.3', 'S1', 'done', 'closed')")

cur.execute("INSERT INTO agents (id, standby_since, status, pid, heartbeat_at, blocked_reason, updated_at) VALUES ('AGENT_SA', '2026-02-19T00:00:00Z', 'standing_by', NULL, '2026-02-19T00:00:00Z', NULL, '2026-02-19T00:00:00Z')")
cur.execute("INSERT INTO agents (id, standby_since, status, pid, heartbeat_at, blocked_reason, updated_at) VALUES ('AGENT_SB', '2026-02-19T00:00:00Z', 'standing_by', NULL, '2026-02-19T00:00:00Z', NULL, '2026-02-19T00:00:00Z')")
cur.execute("INSERT INTO agents (id, standby_since, status, pid, heartbeat_at, blocked_reason, updated_at) VALUES ('AGENT_SC', '2026-02-19T00:00:00Z', 'blocked', NULL, '2026-02-19T00:00:00Z', 'blocked_for_test', '2026-02-19T00:00:00Z')")

cur.execute(
    """INSERT INTO assignments
       (checkbox_ref, agent_ref, status, created_at, started_at, commit_sha, completed_at, lease_token, lease_expires_at, last_heartbeat_at)
       VALUES ('S1.1', 'AGENT_SB', 'assigned', '2026-02-19T00:00:00Z', '2026-02-19T00:00:00Z', NULL, NULL, 'lease-s1', '2099-01-01T00:00:00Z', '2026-02-19T00:00:00Z')"""
)
cur.execute("UPDATE agents SET status = 'busy' WHERE id = 'AGENT_SB'")
cur.execute("UPDATE agents SET heartbeat_at = datetime('now'), updated_at = datetime('now') WHERE id = 'AGENT_SA'")

conn.commit()
conn.close()
`,
  )
}

describe("control-plane status surface", () => {
  it("returns fleet snapshots via --all --json", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-status-"))
    const dbPath = path.join(tmp, "ledger.db")
    seedStatusFixture(dbPath)

    const run = spawnSync("./control-plane/status.sh", ["--all", "--json"], {
      cwd: ROOT,
      env: {
        ...process.env,
        CICSC_LEDGER_DB_PATH: dbPath,
      },
      encoding: "utf8",
    })

    assert.equal(run.status, 0, run.stderr || run.stdout)
    const snapshots = JSON.parse(run.stdout)
    assert.equal(Array.isArray(snapshots), true)
    assert.equal(snapshots.length, 3)

    const ids = new Set(snapshots.map((s: any) => s.agent_id))
    assert.equal(ids.has("AGENT_SA"), true)
    assert.equal(ids.has("AGENT_SB"), true)
    assert.equal(ids.has("AGENT_SC"), true)
  })

  it("returns canonical aggregates via --summary --json", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-status-"))
    const dbPath = path.join(tmp, "ledger.db")
    seedStatusFixture(dbPath)

    const run = spawnSync("./control-plane/status.sh", ["--summary", "--json"], {
      cwd: ROOT,
      env: {
        ...process.env,
        CICSC_LEDGER_DB_PATH: dbPath,
      },
      encoding: "utf8",
    })

    assert.equal(run.status, 0, run.stderr || run.stdout)
    const summary = JSON.parse(run.stdout)
    assert.equal(summary.total_agents, 3)
    assert.equal(summary.standing_by, 1)
    assert.equal(summary.busy, 1)
    assert.equal(summary.blocked, 1)
    assert.equal(summary.assignable_idle_count, 1)
    assert.equal(summary.assigned_count, 1)
    assert.equal(summary.open_count, 2)
    assert.equal(summary.unassigned_open_count, 1)
    assert.equal(summary.stale_lease_count, 0)
  })
})
