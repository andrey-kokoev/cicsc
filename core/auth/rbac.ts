import { SpecV0, SpecRoleV0 } from "../../../spec/ast"

export class RBACEngine {
  constructor(private spec: SpecV0) { }

  /**
   * Checks if an internal user with specific roles and context has permission.
   */
  canExecute (userRoles: string[], action: string, resource: string, context: { entityName?: string, actorId?: string, row?: any } = {}): boolean {
    const { entityName, actorId, row } = context
    // 1. Resolve full set of roles (including inheritance)
    const allRoles = this.expandRoles(userRoles)

    // 2. If it's a command on an entity
    if (entityName && action === "command") {
      const entity = this.spec.entities[entityName]
      const command = entity?.commands?.[resource]
      if (!command) return false

      if (!command.permissions || command.permissions.length === 0) return true

      // Special handling for dynamic roles (ABAC)
      if (command.permissions.includes("Owner") && row && actorId) {
        if (row.owner_id === actorId || row.creator_id === actorId) return true
      }

      return command.permissions.some(r => allRoles.has(r))
    }

    // 3. If it's a view
    if (action === "view") {
      const view = this.spec.views?.[resource]
      if (!view) return false
      if (!view.permissions || view.permissions.length === 0) return true
      return view.permissions.some(r => allRoles.has(r))
    }

    return false
  }

  private expandRoles (userRoles: string[]): Set<string> {
    const expanded = new Set<string>(userRoles)
    let added = true
    while (added) {
      added = false
      for (const roleId of Array.from(expanded)) {
        const roleDef = this.spec.roles?.[roleId]
        if (roleDef?.inherits) {
          for (const parent of roleDef.inherits) {
            if (!expanded.has(parent)) {
              expanded.add(parent)
              added = true
            }
          }
        }
      }
    }
    return expanded
  }
}
