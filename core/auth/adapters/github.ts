import { AuthProvider, UserProfile, AuthError } from "../types"

export class GithubProvider implements AuthProvider {
  readonly id = "github";

  async validateToken (token: string): Promise<UserProfile> {
    try {
      const response = await fetch("https://api.github.com/user", {
        headers: {
          Authorization: `token ${token}`,
          Accept: "application/json",
          "User-Agent": "CICSC-Agent"
        }
      })

      if (!response.ok) {
        throw new AuthError(this.id, "Failed to fetch GitHub user")
      }

      const payload = await response.json()

      return {
        id: payload.id.toString(),
        email: payload.email,
        name: payload.name || payload.login,
        avatarUrl: payload.avatar_url,
        raw: payload
      }
    } catch (err: any) {
      throw new AuthError(this.id, err.message)
    }
  }
}
