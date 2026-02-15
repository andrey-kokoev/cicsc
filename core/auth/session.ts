import { UserProfile } from "./types"

export interface Session {
  sessionId: string
  userId: string
  provider: string
  profile: UserProfile
  expiresAt: number
}

export class SessionStore {
  private sessions: Map<string, Session> = new Map();

  createSession (profile: UserProfile, provider: string, ttlSeconds: number = 3600): Session {
    const sessionId = Math.random().toString(36).substring(2) + Date.now().toString(36)
    const session: Session = {
      sessionId,
      userId: profile.id,
      provider,
      profile,
      expiresAt: Date.now() + (ttlSeconds * 1000)
    }
    this.sessions.set(sessionId, session)
    return session
  }

  getSession (sessionId: string): Session | null {
    const session = this.sessions.get(sessionId)
    if (!session) return null
    if (Date.now() > session.expiresAt) {
      this.sessions.delete(sessionId)
      return null
    }
    return session
  }

  revoke (sessionId: string) {
    this.sessions.delete(sessionId)
  }
}
