import { AuthProvider, UserProfile, AuthError } from "../types"

export interface MicrosoftConfig {
  tenantId: string
  clientId: string
}

export class MicrosoftProvider implements AuthProvider {
  readonly id = "microsoft"

  constructor(private config: MicrosoftConfig) { }

  async validateToken(token: string): Promise<UserProfile> {
    try {
      // Microsoft Graph API for user info
      const userInfoUrl = "https://graph.microsoft.com/v1.0/me"

      const response = await fetch(userInfoUrl, {
        headers: {
          Authorization: `Bearer ${token}`
        }
      })

      if (!response.ok) {
        throw new AuthError(this.id, "Invalid Microsoft token or Graph API unreachable")
      }

      const payload = await response.json()

      return {
        id: payload.id,
        email: payload.mail || payload.userPrincipalName,
        name: payload.displayName,
        provider: this.id,
        raw: payload
      }
    } catch (error) {
      if (error instanceof AuthError) throw error
      throw new AuthError(this.id, `Token validation failed: ${error}`)
    }
  }
}
