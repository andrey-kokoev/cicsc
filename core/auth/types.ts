export interface UserProfile {
  id: string // The provider-specific unique ID
  email?: string
  name?: string
  avatarUrl?: string
  raw: any // The raw response from the provider
}

export interface AuthProvider {
  id: string // e.g., 'google', 'github'
  validateToken (token: string): Promise<UserProfile>
}

export class AuthError extends Error {
  constructor(public provider: string, message: string) {
    super(`[AuthError:${provider}] ${message}`)
  }
}
