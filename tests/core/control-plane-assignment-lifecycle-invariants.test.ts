import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import os from "node:os"
import path from "node:path"
import { spawnSync } from "node:child_process"

type SeedOptions = {
  checkboxStatus: "open" | "done"
  assignmentStatus: "assigned" | "done"
  agentStatus?: "standing_by" | "busy" | "blocked"
  blockedReason?: string
  includeLease?: boolean
  includeCommit?: boolean
}

function seedLedgerDb(dbPath: string, opts: SeedOptions): void {
  const py = `
import sqlite3
import sys

db_path = sys.argv[1]
checkbox_status = sys.argv[2]
assignment_status = sys.argv[3]
agent_status = sys.argv[4]
blocked_reason = sys.argv[5]
include_lease = sys.argv[6] == "1"
include_commit = sys.argv[7] == "1"

conn = sqlite3.connect(db_path)
cur = conn.cursor()

cur.execute("""CREATE TABLE phases (
    id TEXT PRIMARY KEY,
    number INTEGER,
    status TEXT,
    title TEXT,
    description TEXT
)""")
cur.execute("""CREATE TABLE milestones (
    id TEXT PRIMARY KEY,
    phase_id TEXT,
    title TEXT
)""")
cur.execute("""CREATE TABLE checkboxes (
    id TEXT PRIMARY KEY,
    milestone_id TEXT,
    status TEXT,
    description TEXT
)""")
cur.execute("""CREATE TABLE assignments (
    checkbox_ref TEXT PRIMARY KEY,
    agent_ref TEXT,
    status TEXT,
    created_at TEXT,
    started_at TEXT,
    commit_sha TEXT,
    completed_at TEXT,
    lease_token TEXT,
    lease_expires_at TEXT,
    last_heartbeat_at TEXT
)""")
cur.execute("""CREATE TABLE agents (
    id TEXT PRIMARY KEY,
    standby_since TEXT,
    status TEXT,
    pid INTEGER,
    heartbeat_at TEXT,
    blocked_reason TEXT,
    updated_at TEXT
)""")
cur.execute("""CREATE TABLE events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    event_type TEXT,
    type TEXT,
    checkbox_ref TEXT,
    agent_ref TEXT,
    lease_token TEXT,
    timestamp TEXT,
    details TEXT
)""")

cur.execute(
    "INSERT INTO phases (id, number, status, title, description) VALUES (?, ?, ?, ?, ?)",
    ("T", 1, "in_progress", "Test Phase", ""),
)
cur.execute(
    "INSERT INTO milestones (id, phase_id, title) VALUES (?, ?, ?)",
    ("T1", "T", "Milestone T1"),
)
cur.execute(
    "INSERT INTO checkboxes (id, milestone_id, status, description) VALUES (?, ?, ?, ?)",
    ("T1.1", "T1", checkbox_status, "test checkbox"),
)
cur.execute(
    "INSERT INTO agents (id, standby_since, status, pid, heartbeat_at, blocked_reason, updated_at) VALUES (?, ?, ?, ?, ?, ?, ?)",
    ("AGENT_TEST", "2026-02-19T00:00:00Z", agent_status, 1234, "2026-02-19T00:00:00Z", blocked_reason or None, "2026-02-19T00:00:00Z"),
)

lease_token = "lease-token" if include_lease and assignment_status == "assigned" else None
lease_expires = "2099-01-01T00:00:00Z" if include_lease and assignment_status == "assigned" else None
last_hb = "2026-02-19T00:00:00Z" if include_lease and assignment_status == "assigned" else None
commit_sha = "abc1234" if include_commit and assignment_status == "done" else None
completed_at = "2026-02-19T00:01:00Z" if include_commit and assignment_status == "done" else None

cur.execute(
    """INSERT INTO assignments
    (checkbox_ref, agent_ref, status, created_at, started_at, commit_sha, completed_at, lease_token, lease_expires_at, last_heartbeat_at)
    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)""",
    ("T1.1", "AGENT_TEST", assignment_status, "2026-02-19T00:00:00Z", "2026-02-19T00:00:00Z", commit_sha, completed_at, lease_token, lease_expires, last_hb),
)

conn.commit()
conn.close()
`

  const run = spawnSync(
    "python3",
    [
      "-c",
      py,
      dbPath,
      opts.checkboxStatus,
      opts.assignmentStatus,
      opts.agentStatus ?? (opts.assignmentStatus === "assigned" ? "busy" : "standing_by"),
      opts.blockedReason ?? "",
      opts.includeLease === false ? "0" : "1",
      opts.includeCommit === false ? "0" : "1",
    ],
    {
      cwd: process.cwd(),
      encoding: "utf8",
    },
  )
  assert.equal(run.status, 0, run.stderr || run.stdout)
}

function runValidate(dbPath: string): ReturnType<typeof spawnSync> {
  return spawnSync("./control-plane/validate.sh", {
    cwd: process.cwd(),
    env: {
      ...process.env,
      CICSC_LEDGER_DB_PATH: dbPath,
    },
    encoding: "utf8",
  })
}

describe("control-plane assignment lifecycle invariants", () => {
  it("accepts assigned assignment with open checkbox", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-ledger-"))
    const dbPath = path.join(tmp, "ledger.db")
    seedLedgerDb(dbPath, { checkboxStatus: "open", assignmentStatus: "assigned" })

    const run = runValidate(dbPath)
    assert.equal(run.status, 0, run.stderr || run.stdout)
  })

  it("rejects done assignment when checkbox remains open", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-ledger-"))
    const dbPath = path.join(tmp, "ledger.db")
    seedLedgerDb(dbPath, { checkboxStatus: "open", assignmentStatus: "done" })

    const run = runValidate(dbPath)
    assert.notEqual(run.status, 0)
    assert.match(run.stderr, /assignment .* is done but checkbox is open/i)
  })

  it("rejects active assignment when checkbox is already done", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-ledger-"))
    const dbPath = path.join(tmp, "ledger.db")
    seedLedgerDb(dbPath, { checkboxStatus: "done", assignmentStatus: "assigned" })

    const run = runValidate(dbPath)
    assert.notEqual(run.status, 0)
    assert.match(run.stderr, /done but has active assignment/i)
  })

  it("rejects standing_by agent with active assignment", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-ledger-"))
    const dbPath = path.join(tmp, "ledger.db")
    seedLedgerDb(dbPath, {
      checkboxStatus: "open",
      assignmentStatus: "assigned",
      agentStatus: "standing_by",
    })

    const run = runValidate(dbPath)
    assert.notEqual(run.status, 0)
    assert.match(run.stderr, /standing_by with .*active assignments/i)
  })

  it("rejects blocked agent without reason", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-ledger-"))
    const dbPath = path.join(tmp, "ledger.db")
    seedLedgerDb(dbPath, {
      checkboxStatus: "open",
      assignmentStatus: "assigned",
      agentStatus: "blocked",
      blockedReason: "",
    })

    const run = runValidate(dbPath)
    assert.notEqual(run.status, 0)
    assert.match(run.stderr, /blocked without blocked_reason/i)
  })
})
