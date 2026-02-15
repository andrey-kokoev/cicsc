import { AuthProvider, UserProfile, AuthError } from "../types"

export interface OIDCConfig {
  issuerBaseURL: string
  clientId: string
}

export class OIDCProvider implements AuthProvider {
  readonly id = "oidc";

  constructor(private config: OIDCConfig) { }

  async validateToken (token: string): Promise<UserProfile> {
    try {
      // Standard OIDC userinfo endpoint discovery would normally be used here.
      // For the adapter logic, we assume the token is a validated JWT 
      // or we hit the userinfo endpoint of the issuer.
      const userInfoUrl = `${this.config.issuerBaseURL}/oauth2/v1/userinfo`

      const response = await fetch(userInfoUrl, {
        headers: {
          Authorization: `Bearer ${token}`
        }
      })

      if (!response.ok) {
        throw new AuthError(this.id, "Invalid OIDC token or issuer unreachable")
      }

      const payload = await response.json()

      return {
        id: payload.sub,
        email: payload.email,
        name: payload.name || payload.preferred_username,
        raw: payload
      }
    } catch (err: any) {
      throw new AuthError(this.id, err.message)
    }
  }
}
