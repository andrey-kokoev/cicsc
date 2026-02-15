import { AuthProvider, UserProfile, AuthError } from "./types"

export class AuthManager {
  private providers: Map<string, AuthProvider> = new Map();

  registerProvider (provider: AuthProvider) {
    this.providers.set(provider.id, provider)
  }

  async validate (providerId: string, token: string): Promise<UserProfile> {
    const provider = this.providers.get(providerId)
    if (!provider) {
      throw new AuthError("manager", `Provider '${providerId}' not registered`)
    }
    return provider.validateToken(token)
  }

  getProviders (): string[] {
    return Array.from(this.providers.keys())
  }
}
