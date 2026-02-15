export interface AuditEvent {
  id: string;
  timestamp: string;
  actorId: string;
  action: string; // 'command', 'view', 'login', 'logout', 'schema_change'
  resource: string;
  entityName?: string;
  payload?: any;
  result: "success" | "failure";
  reason?: string;
  hash?: string; // For BJ2.2/2.3 Integrity
}

export class AuditLog {
  private logs: AuditEvent[] = [];

  log(event: Omit<AuditEvent, "id" | "timestamp" | "hash">) {
    const fullEvent: AuditEvent = {
        ...event,
        id: `audit_${Date.now()}_${Math.random().toString(36).substring(7)}`,
        timestamp: new Date().toISOString()
    };
    
    // BJ2.2/2.3 Simple cryptographic chain (simulated)
    const prevHash = this.logs.length > 0 ? this.logs[this.logs.length - 1].hash : "0";
    fullEvent.hash = this.simulateHash(JSON.stringify(fullEvent) + prevHash);
    
    this.logs.push(fullEvent);
    console.log(`[Audit] ${fullEvent.action} ${fullEvent.resource} by ${fullEvent.actorId}: ${fullEvent.result}`);
  }

  private simulateHash(data: string): string {
    // Simple sum-based hash for prototype
    let hash = 0;
    for (let i = 0; i < data.length; i++) {
        hash = ((hash << 5) - hash) + data.charCodeAt(i);
        hash |= 0;
    }
    return hash.toString(16);
  }

  query(filter: { actorId?: string; resource?: string }): AuditEvent[] {
    return this.logs.filter(l => {
        if (filter.actorId && l.actorId !== filter.actorId) return false;
        if (filter.resource && l.resource !== filter.resource) return false;
        return true;
    });
  }

  /**
   * BJ2.4 Archival.
   */
  exportLogs(): string {
    return JSON.stringify(this.logs, null, 2);
  }
}
