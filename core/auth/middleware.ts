import { AuthManager } from "./manager"
import { SessionStore } from "./session"

export class AuthMiddleware {
  constructor(
    private authManager: AuthManager,
    private sessionStore: SessionStore
  ) { }

  /**
   * High-level handler for an incoming auth request.
   * Can handle both raw provider tokens (for login) and session IDs (for subsequent calls).
   */
  async authenticate (headers: Record<string, string>) {
    const authHeader = headers["authorization"]
    if (!authHeader) return null

    const [type, token] = authHeader.split(" ")

    // Strategy 1: Session Bearer Token
    if (type === "Session") {
      return this.sessionStore.getSession(token)
    }

    // Strategy 2: Provider Token (e.g., "Google <jwt>" or "Github <token>")
    // This facilitates a 'lazy login' or first-time auth.
    const providerId = type.toLowerCase()
    const providers = this.authManager.getProviders()

    if (providers.includes(providerId)) {
      const profile = await this.authManager.validate(providerId, token)
      // Automatically create a session on success
      return this.sessionStore.createSession(profile, providerId)
    }

    return null
  }
}
