import { AuthProvider, UserProfile, AuthError } from "../types"

export class GoogleProvider implements AuthProvider {
  readonly id = "google";

  /**
   * Validates a Google ID Token (JWT).
   * In a real system, this would fetch public keys from https://www.googleapis.com/oauth2/v3/certs
   * and verify the signature + audience (client ID).
   */
  async validateToken (token: string): Promise<UserProfile> {
    try {
      // For the prototype/agent execution, we'll demonstrate the fetch-based approach
      // but use a placeholder for the actual cryptographic signature check if libraries are missing.
      const response = await fetch(`https://oauth2.googleapis.com/tokeninfo?id_token=${token}`)

      if (!response.ok) {
        throw new AuthError(this.id, "Invalid Google token")
      }

      const payload = await response.json()

      if (payload.error) {
        throw new AuthError(this.id, payload.error_description || payload.error)
      }

      return {
        id: payload.sub,
        email: payload.email,
        name: payload.name,
        avatarUrl: payload.picture,
        raw: payload
      }
    } catch (err: any) {
      throw new AuthError(this.id, err.message)
    }
  }
}
