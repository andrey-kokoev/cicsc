import { UserProfile } from "./types"

export interface IdentityMap {
  internalUserId: string
  externalProviderId: string
  externalUserId: string
  lastSync: number
}

export class IdentitySyncService {
  private identityMap: Map<string, IdentityMap> = new Map(); // Key: provider:extId
  private userAttributes: Map<string, any> = new Map(); // Key: internalUserId

  /**
   * Resolves an external profile to an internal user ID.
   * If the user doesn't exist, it provisions one (BH3.4).
   */
  resolveUser (profile: UserProfile, provider: string): string {
    const key = `${provider}:${profile.id}`
    let mapping = this.identityMap.get(key)

    if (!mapping) {
      // Provisioning (BH3.4)
      const internalId = `u_${Math.random().toString(36).substring(7)}`
      mapping = {
        internalUserId: internalId,
        externalProviderId: provider,
        externalUserId: profile.id,
        lastSync: Date.now()
      }
      this.identityMap.set(key, mapping)
      console.log(`[IdentitySync] Provisioned new internal user ${internalId} for ${key}`)
    }

    // Attribute Sync (BH3.2)
    this.syncAttributes(mapping.internalUserId, profile)
    mapping.lastSync = Date.now()

    return mapping.internalUserId
  }

  private syncAttributes (internalUserId: string, profile: UserProfile) {
    const attrs = {
      email: profile.email,
      name: profile.name,
      avatar: profile.avatarUrl,
      updatedAt: Date.now()
    }
    this.userAttributes.set(internalUserId, attrs)
  }

  getUser (internalUserId: string) {
    return this.userAttributes.get(internalUserId)
  }

  /**
   * Multi-provider linking (BH3.3).
   * Links a new provider account to an existing internal user.
   */
  linkIdentity (internalUserId: string, profile: UserProfile, provider: string) {
    const key = `${provider}:${profile.id}`
    if (this.identityMap.has(key)) {
      throw new Error(`External identity ${key} is already linked to another user`)
    }

    this.identityMap.set(key, {
      internalUserId,
      externalProviderId: provider,
      externalUserId: profile.id,
      lastSync: Date.now()
    })
  }
}
