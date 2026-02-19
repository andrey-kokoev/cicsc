import { describe, it } from "node:test"
import assert from "node:assert/strict"
import fs from "node:fs"
import os from "node:os"
import path from "node:path"
import { spawn, spawnSync, type ChildProcess } from "node:child_process"

const ROOT = process.cwd()

function wait(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms))
}

function waitForExit(proc: ChildProcess, timeoutMs: number): Promise<{ code: number | null; signal: NodeJS.Signals | null }> {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => reject(new Error("process did not exit in time")), timeoutMs)
    proc.once("exit", (code, signal) => {
      clearTimeout(timer)
      resolve({ code, signal })
    })
  })
}

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

function seedBase(dbPath: string): void {
  runPy(
    dbPath,
    `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute("INSERT INTO phases (id, number, status, title, description) VALUES ('T', 1, 'in_progress', 'Test', '')")
cur.execute("INSERT INTO milestones (id, phase_id, title) VALUES ('T1', 'T', 'Milestone')")
conn.commit()
conn.close()
`,
  )
}

function insertCheckbox(dbPath: string, checkboxId: string): void {
  runPy(
    dbPath,
    `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute("INSERT INTO checkboxes (id, milestone_id, status, description) VALUES (?, 'T1', 'open', 'task')", ('${checkboxId}',))
conn.commit()
conn.close()
`,
  )
}

function upsertAgent(dbPath: string, agentId: string, status: "standing_by" | "busy" | "blocked", blockedReason = ""): void {
  runPy(
    dbPath,
    `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute("DELETE FROM agents WHERE id = ?", ('${agentId}',))
cur.execute(
    """INSERT INTO agents (id, standby_since, status, pid, heartbeat_at, blocked_reason, updated_at)
       VALUES (?, '2026-02-19T00:00:00Z', ?, NULL, '2026-02-19T00:00:00Z', ?, '2026-02-19T00:00:00Z')""",
    ('${agentId}', '${status}', '${blockedReason}')
)
conn.commit()
conn.close()
`,
  )
}

function insertAssigned(dbPath: string, checkboxId: string, agentId: string, leaseExpiresAt: string, lastHeartbeatAt: string): void {
  runPy(
    dbPath,
    `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute(
    """INSERT INTO assignments
       (checkbox_ref, agent_ref, status, created_at, started_at, commit_sha, completed_at, lease_token, lease_expires_at, last_heartbeat_at)
       VALUES (?, ?, 'assigned', '2026-02-19T00:00:00Z', '2026-02-19T00:00:00Z', NULL, NULL, 'lease-x', ?, ?)""",
    ('${checkboxId}', '${agentId}', '${leaseExpiresAt}', '${lastHeartbeatAt}')
)
conn.commit()
conn.close()
`,
  )
}

function assignmentCount(dbPath: string): number {
  const out = runPy(
    dbPath,
    `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute("SELECT COUNT(*) FROM assignments WHERE status = 'assigned'")
print(cur.fetchone()[0])
conn.close()
`,
  )
  return Number(out.trim())
}

describe("control-plane agentd protocol", () => {
  it("enforces one daemon process per agent id", async () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-agentd-"))
    const dbPath = path.join(tmp, "ledger.db")

    seedBase(dbPath)
    upsertAgent(dbPath, "AGENT_T1", "standing_by")

    const env = {
      ...process.env,
      CICSC_LEDGER_DB_PATH: dbPath,
    }

    const daemon = spawn(
      "./control-plane/agentd.sh",
      ["run", "--agent", "AGENT_T1", "--poll-seconds", "1", "--lease-seconds", "5"],
      { cwd: ROOT, env, stdio: "pipe" },
    )

    await wait(1200)

    const second = spawnSync(
      "./control-plane/agentd.sh",
      ["run", "--agent", "AGENT_T1", "--poll-seconds", "1", "--lease-seconds", "5"],
      { cwd: ROOT, env, encoding: "utf8", timeout: 5000 },
    )
    assert.equal(second.status, 0, second.stderr || second.stdout)
    assert.match(`${second.stdout}${second.stderr}`, /already running/i)

    const status = spawnSync("./control-plane/status.sh", ["--agent", "AGENT_T1", "--json"], {
      cwd: ROOT,
      env,
      encoding: "utf8",
    })
    assert.equal(status.status, 0, status.stderr || status.stdout)
    const snapshot = JSON.parse(status.stdout)
    assert.equal(snapshot.status, "standing_by")
    assert.equal(snapshot.exists, true)

    const stop = spawnSync("./control-plane/agentd.sh", ["stop", "--agent", "AGENT_T1"], {
      cwd: ROOT,
      env,
      encoding: "utf8",
    })
    assert.equal(stop.status, 0, stop.stderr || stop.stdout)

    const exited = await waitForExit(daemon, 7000)
    assert.equal(exited.code, 0)
  })

  it("stop while assigned retains assignment ownership", async () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-agentd-"))
    const dbPath = path.join(tmp, "ledger.db")

    seedBase(dbPath)
    insertCheckbox(dbPath, "T1.1")
    upsertAgent(dbPath, "AGENT_T2", "standing_by")
    insertAssigned(dbPath, "T1.1", "AGENT_T2", "2099-01-01T00:00:00Z", "2026-02-19T00:00:00Z")

    const env = {
      ...process.env,
      CICSC_LEDGER_DB_PATH: dbPath,
    }

    const daemon = spawn(
      "./control-plane/agentd.sh",
      ["run", "--agent", "AGENT_T2", "--poll-seconds", "1", "--lease-seconds", "5"],
      { cwd: ROOT, env, stdio: "pipe" },
    )

    await wait(1200)

    const stop = spawnSync("./control-plane/agentd.sh", ["stop", "--agent", "AGENT_T2"], {
      cwd: ROOT,
      env,
      encoding: "utf8",
    })
    assert.equal(stop.status, 0, stop.stderr || stop.stdout)

    await waitForExit(daemon, 7000)

    const status = spawnSync("./control-plane/status.sh", ["--agent", "AGENT_T2", "--json"], {
      cwd: ROOT,
      env,
      encoding: "utf8",
    })
    assert.equal(status.status, 0, status.stderr || status.stdout)

    const snapshot = JSON.parse(status.stdout)
    assert.equal(snapshot.status, "blocked")
    assert.equal(snapshot.assignment.checkbox_ref, "T1.1")
  })

  it("autoassign does not assign to non-standing_by agents", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-agentd-"))
    const dbPath = path.join(tmp, "ledger.db")

    seedBase(dbPath)
    insertCheckbox(dbPath, "T1.2")
    upsertAgent(dbPath, "AGENT_T3", "busy")

    const env = {
      ...process.env,
      CICSC_LEDGER_DB_PATH: dbPath,
    }

    const first = spawnSync("./control-plane/autoassign.sh", [], { cwd: ROOT, env, encoding: "utf8" })
    assert.equal(first.status, 0, first.stderr || first.stdout)
    assert.equal(assignmentCount(dbPath), 0)

    runPy(
      dbPath,
      `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute("UPDATE agents SET status = 'standing_by', heartbeat_at = datetime('now'), updated_at = datetime('now') WHERE id = 'AGENT_T3'")
conn.commit()
conn.close()
`,
    )

    const second = spawnSync("./control-plane/autoassign.sh", [], { cwd: ROOT, env, encoding: "utf8" })
    assert.equal(second.status, 0, second.stderr || second.stdout)
    assert.equal(assignmentCount(dbPath), 1)
  })

  it("autoassign reclaims stale leases for non-blocked agents", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-agentd-"))
    const dbPath = path.join(tmp, "ledger.db")

    seedBase(dbPath)
    insertCheckbox(dbPath, "T1.3")
    upsertAgent(dbPath, "AGENT_T4", "standing_by")
    insertAssigned(dbPath, "T1.3", "AGENT_T4", "2001-01-01T00:00:00Z", "2001-01-01T00:00:00Z")
    runPy(
      dbPath,
      `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute("UPDATE agents SET status = 'busy', updated_at = datetime('now') WHERE id = 'AGENT_T4'")
conn.commit()
conn.close()
`,
    )

    const env = {
      ...process.env,
      CICSC_LEDGER_DB_PATH: dbPath,
    }

    const run = spawnSync("./control-plane/autoassign.sh", [], { cwd: ROOT, env, encoding: "utf8" })
    assert.equal(run.status, 0, run.stderr || run.stdout)
    assert.equal(assignmentCount(dbPath), 0)

    const reclaimed = runPy(
      dbPath,
      `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute("SELECT COUNT(*) FROM events WHERE event_type = 'assignment_reclaimed'")
print(cur.fetchone()[0])
conn.close()
`,
    )
    assert.equal(Number(reclaimed.trim()) >= 1, true)
  })

  it("integrate command requires explicit --agent", () => {
    const run = spawnSync("./control-plane/integrate.sh", ["integrate", "T1.1"], {
      cwd: ROOT,
      encoding: "utf8",
    })
    assert.notEqual(run.status, 0)
    assert.match(`${run.stdout}${run.stderr}`, /--agent is required|Usage/i)
  })

  it("integrate rejects removed convenience modes", () => {
    const statusRun = spawnSync("./control-plane/integrate.sh", ["status"], {
      cwd: ROOT,
      encoding: "utf8",
    })
    assert.notEqual(statusRun.status, 0)
    assert.match(`${statusRun.stdout}${statusRun.stderr}`, /Usage/i)

    const fromBranchRun = spawnSync(
      "./control-plane/integrate.sh",
      ["integrate", "--from-branch", "feat/CHQ1.1", "--agent", "AGENT_X"],
      {
        cwd: ROOT,
        encoding: "utf8",
      },
    )
    assert.notEqual(fromBranchRun.status, 0)
    assert.match(`${fromBranchRun.stdout}${fromBranchRun.stderr}`, /Unexpected extra argument|Usage/i)
  })

  it("strict assignment ownership rejects mismatched agent and accepts owner", () => {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "cicsc-agentd-"))
    const dbPath = path.join(tmp, "ledger.db")

    seedBase(dbPath)
    insertCheckbox(dbPath, "T1.4")
    upsertAgent(dbPath, "AGENT_OWNER", "standing_by")
    upsertAgent(dbPath, "AGENT_OTHER", "standing_by")
    insertAssigned(dbPath, "T1.4", "AGENT_OWNER", "2099-01-01T00:00:00Z", "2026-02-19T00:00:00Z")

    const mismatch = runPy(
      dbPath,
      `
import sys
sys.path.insert(0, 'control-plane')
from db import complete_assignment

print(complete_assignment('T1.4', 'abc1234', expected_agent='AGENT_OTHER'))
`,
    )
    assert.equal(mismatch.trim(), "False")

    const mismatchState = runPy(
      dbPath,
      `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute("SELECT status FROM assignments WHERE checkbox_ref = 'T1.4'")
print(cur.fetchone()[0])
conn.close()
`,
    )
    assert.equal(mismatchState.trim(), "assigned")

    const owner = runPy(
      dbPath,
      `
import sys
sys.path.insert(0, 'control-plane')
from db import complete_assignment

print(complete_assignment('T1.4', 'abc5678', expected_agent='AGENT_OWNER'))
`,
    )
    assert.equal(owner.trim(), "True")

    const finalState = runPy(
      dbPath,
      `
import sys
sys.path.insert(0, 'control-plane')
from db import get_db

conn = get_db()
cur = conn.cursor()
cur.execute("SELECT status, commit_sha FROM assignments WHERE checkbox_ref = 'T1.4'")
assignment = cur.fetchone()
cur.execute("SELECT status FROM checkboxes WHERE id = 'T1.4'")
checkbox = cur.fetchone()
print(assignment[0], assignment[1], checkbox[0])
conn.close()
`,
    )
    assert.match(finalState.trim(), /^done abc5678 done$/)
  })

  it("runs gates only in worker close path, not in integrate", () => {
    const workerScript = fs.readFileSync(path.join(ROOT, "control-plane/worker-run-assignment.sh"), "utf8")
    const integrateScript = fs.readFileSync(path.join(ROOT, "control-plane/integrate.sh"), "utf8")
    assert.match(workerScript, /check_gates\.sh/)
    assert.doesNotMatch(integrateScript, /check_gates\.sh/)
  })

  it("removes legacy file-based collaboration scripts", () => {
    assert.equal(fs.existsSync(path.join(ROOT, "control-plane", `submit_collab_issue${".sh"}`)), false)
    assert.equal(fs.existsSync(path.join(ROOT, "control-plane", `respond_collab_issue${".sh"}`)), false)
    assert.equal(fs.existsSync(path.join(ROOT, "control-plane", `get_open_collab_issues${".sh"}`)), false)
  })

  it("removes deprecated command surfaces", () => {
    assert.equal(fs.existsSync(path.join(ROOT, "control-plane", "standby.sh")), false)
    assert.equal(fs.existsSync(path.join(ROOT, "control-plane", "main-close.sh")), false)
    assert.equal(fs.existsSync(path.join(ROOT, "control-plane", "onboard.sh")), false)
  })
})
