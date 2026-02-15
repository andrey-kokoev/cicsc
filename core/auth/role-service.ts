export class RoleService {
  private userRoles: Map<string, Set<string>> = new Map();

  assignRole (userId: string, roleId: string) {
    if (!this.userRoles.has(userId)) {
      this.userRoles.set(userId, new Set())
    }
    this.userRoles.get(userId)!.add(roleId)
  }

  removeRole (userId: string, roleId: string) {
    this.userRoles.get(userId)?.delete(roleId)
  }

  getRoles (userId: string): string[] {
    return Array.from(this.userRoles.get(userId) || [])
  }

  /**
   * BH3.4 Account deprovisioning.
   */
  clearUser (userId: string) {
    this.userRoles.delete(userId)
  }
}
