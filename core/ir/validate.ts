// /core/ir/validate.ts

import type { CoreIrBundleV0, CoreIrV0, EntityTypeSpecV0, ExprV0, QueryV0, ReducerOpV0 } from "./types"
import { typecheckCoreIrV0 } from "./typecheck"

export type ValidationError = {
  path: string
  message: string
}

export function validateBundleV0 (bundle: unknown): { ok: true; value: CoreIrBundleV0 } | { ok: false; errors: ValidationError[] } {
  const errors: ValidationError[] = []
  const b = bundle as any

  if (!isObject(b)) return fail(errors, "$", "bundle must be an object")

  if (!isObject(b.core_ir)) return fail(errors, "$.core_ir", "core_ir must be an object")

  const ir = b.core_ir as any
  if (ir.version !== 0) errors.push({ path: "$.core_ir.version", message: "core_ir.version must be 0" })

  if (!isObject(ir.types)) errors.push({ path: "$.core_ir.types", message: "core_ir.types must be an object" })
  else {
    for (const [typeName, typeSpec] of Object.entries(ir.types)) {
      validateEntityType(errors, `$.core_ir.types.${typeName}`, typeName, typeSpec as any)
    }
  }

  // light checks for optional blocks
  if (ir.policies != null && !isObject(ir.policies)) errors.push({ path: "$.core_ir.policies", message: "policies must be an object" })
  if (ir.constraints != null && !isObject(ir.constraints)) errors.push({ path: "$.core_ir.constraints", message: "constraints must be an object" })
  if (ir.views != null && !isObject(ir.views)) errors.push({ path: "$.core_ir.views", message: "views must be an object" })
  if (ir.slas != null && !isObject(ir.slas)) errors.push({ path: "$.core_ir.slas", message: "slas must be an object" })

  if (ir.webhooks != null && !isObject(ir.webhooks)) errors.push({ path: "$.core_ir.webhooks", message: "webhooks must be an object" })
  else if (ir.webhooks != null) {
    for (const [hookName, hookSpec] of Object.entries(ir.webhooks)) {
      validateWebhook(errors, `$.core_ir.webhooks.${hookName}`, hookName, hookSpec as any)
    }
  }

  if (ir.slas != null && !isObject(ir.slas)) errors.push({ path: "$.core_ir.slas", message: "slas must be an object" })
  else if (ir.slas != null) {
    for (const [slaName, slaSpec] of Object.entries(ir.slas)) {
      validateSla(errors, `$.core_ir.slas.${slaName}`, slaName, slaSpec as any)
    }
  }

  if (ir.schedules != null && !isObject(ir.schedules)) errors.push({ path: "$.core_ir.schedules", message: "schedules must be an object" })
  else if (ir.schedules != null) {
    for (const [schedName, schedSpec] of Object.entries(ir.schedules)) {
      validateSchedule(errors, `$.core_ir.schedules.${schedName}`, schedName, schedSpec as any)
    }
  }

  if (ir.workflows != null && !isObject(ir.workflows)) errors.push({ path: "$.core_ir.workflows", message: "workflows must be an object" })
  else if (ir.workflows != null) {
    for (const [wfName, wfSpec] of Object.entries(ir.workflows)) {
      validateWorkflow(errors, `$.core_ir.workflows.${wfName}`, wfName, wfSpec as any)
    }
  }

  if (ir.multi_entity_commands != null && !isObject(ir.multi_entity_commands)) errors.push({ path: "$.core_ir.multi_entity_commands", message: "multi_entity_commands must be an object" })
  else if (ir.multi_entity_commands != null) {
    for (const [commandName, commandSpec] of Object.entries(ir.multi_entity_commands)) {
      validateMultiEntityCommand(errors, `$.core_ir.multi_entity_commands.${commandName}`, commandName, commandSpec as any)
    }
  }

  if (ir.ui != null && !isObject(ir.ui)) errors.push({ path: "$.core_ir.ui", message: "ui must be an object" })
  else if (ir.ui != null) {
    for (const [uiName, uiSpec] of Object.entries(ir.ui)) {
      validateUiSpec(errors, `$.core_ir.ui.${uiName}`, uiName, uiSpec as any)
    }
  }

  if (ir.services != null && !isObject(ir.services)) errors.push({ path: "$.core_ir.services", message: "services must be an object" })
  else if (ir.services != null) {
    for (const [serviceName, serviceSpec] of Object.entries(ir.services)) {
      validateServiceSpec(errors, `$.core_ir.services.${serviceName}`, serviceName, serviceSpec as any)
    }
  }

  if (ir.migrations != null && !isObject(ir.migrations)) errors.push({ path: "$.core_ir.migrations", message: "migrations must be an object" })
  else if (ir.migrations != null) {
    for (const [migrationName, migrationSpec] of Object.entries(ir.migrations)) {
      validateMigration(errors, `$.core_ir.migrations.${migrationName}`, migrationName, migrationSpec as any)
    }
  }

  if (ir.queues != null && !isObject(ir.queues)) errors.push({ path: "$.core_ir.queues", message: "queues must be an object" })
  else if (ir.queues != null) {
    for (const [qName, qSpec] of Object.entries(ir.queues)) {
      validateQueue(errors, `$.core_ir.queues.${qName}`, qName, qSpec as any)
    }
  }

  if (errors.length) return { ok: false, errors }

  const tc = typecheckCoreIrV0(ir as CoreIrV0)
  if (!tc.ok) {
    return { ok: false, errors: tc.errors.map((e) => ({ path: e.path, message: e.message })) }
  }

  return { ok: true, value: bundle as CoreIrBundleV0 }
}

function validateEntityType (errors: ValidationError[], path: string, typeName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "type spec must be an object" })

  if (spec.id_type !== "string") errors.push({ path: `${path}.id_type`, message: "id_type must be 'string' in v0" })

  if (!Array.isArray(spec.states) || spec.states.some((s: any) => typeof s !== "string")) {
    errors.push({ path: `${path}.states`, message: "states must be string array" })
  } else if (!spec.states.includes(spec.initial_state)) {
    errors.push({ path: `${path}.initial_state`, message: "initial_state must be one of states" })
  }

  if (!isObject(spec.attrs)) errors.push({ path: `${path}.attrs`, message: "attrs must be an object" })
  if (spec.shadows != null && !isObject(spec.shadows)) errors.push({ path: `${path}.shadows`, message: "shadows must be an object" })

  if (!isObject(spec.commands)) errors.push({ path: `${path}.commands`, message: "commands must be an object" })
  else {
    for (const [cmdName, cmdSpec] of Object.entries(spec.commands)) {
      if (!isObject(cmdSpec)) {
        errors.push({ path: `${path}.commands.${cmdName}`, message: "command spec must be an object" })
        continue
      }
      if (!isObject((cmdSpec as any).input)) errors.push({ path: `${path}.commands.${cmdName}.input`, message: "input must be an object" })
      if (!isObject((cmdSpec as any).guard) || (cmdSpec as any).guard.expr == null) {
        errors.push({ path: `${path}.commands.${cmdName}.guard`, message: "guard.expr required" })
      } else {
        validateExpr(errors, `${path}.commands.${cmdName}.guard.expr`, (cmdSpec as any).guard.expr)
      }

      if (!Array.isArray((cmdSpec as any).emits)) {
        errors.push({ path: `${path}.commands.${cmdName}.emits`, message: "emits must be array" })
      } else {
        for (let i = 0; i < (cmdSpec as any).emits.length; i++) {
          const e = (cmdSpec as any).emits[i]
          const ep = `${path}.commands.${cmdName}.emits[${i}]`
          if (!isObject(e)) errors.push({ path: ep, message: "emit must be object" })
          else {
            if (typeof e.event_type !== "string") errors.push({ path: `${ep}.event_type`, message: "event_type must be string" })
            if (!isObject(e.payload)) errors.push({ path: `${ep}.payload`, message: "payload must be object" })
            else for (const [k, ex] of Object.entries(e.payload)) validateExpr(errors, `${ep}.payload.${k}`, ex as any)
          }
        }
      }
    }
  }

  if (!isObject(spec.reducer)) errors.push({ path: `${path}.reducer`, message: "reducer must be an object keyed by event_type" })
  else {
    for (const [evtType, ops] of Object.entries(spec.reducer)) {
      const rp = `${path}.reducer.${evtType}`
      if (!Array.isArray(ops)) errors.push({ path: rp, message: "reducer entry must be array of ops" })
      else ops.forEach((op: any, i: number) => validateReducerOp(errors, `${rp}[${i}]`, op))
    }
  }
}

function validateReducerOp (errors: ValidationError[], path: string, op: any) {
  if (!isObject(op)) return void errors.push({ path, message: "reducer op must be object" })
  const keys = Object.keys(op)
  if (keys.length !== 1) return void errors.push({ path, message: "reducer op must have exactly one tag key" })
  const tag = keys[0]!
  const body = op[tag]

  switch (tag) {
    case "set_state":
      if (!isObject(body) || body.expr == null) errors.push({ path, message: "set_state requires {expr}" })
      else validateExpr(errors, `${path}.set_state.expr`, body.expr)
      break
    case "set_attr":
      if (!isObject(body) || typeof body.name !== "string" || body.expr == null) errors.push({ path, message: "set_attr requires {name,expr}" })
      else validateExpr(errors, `${path}.set_attr.expr`, body.expr)
      break
    case "clear_attr":
      if (!isObject(body) || typeof body.name !== "string") errors.push({ path, message: "clear_attr requires {name}" })
      break
    case "set_shadow":
      if (!isObject(body) || typeof body.name !== "string" || body.expr == null) errors.push({ path, message: "set_shadow requires {name,expr}" })
      else validateExpr(errors, `${path}.set_shadow.expr`, body.expr)
      break
    default:
      errors.push({ path, message: `unknown reducer op tag: ${tag}` })
  }
}

export function validateExpr (errors: ValidationError[], path: string, expr: any) {
  if (!isObject(expr)) return void errors.push({ path, message: "expr must be object" })
  const keys = Object.keys(expr)
  if (keys.length !== 1) return void errors.push({ path, message: "expr must have exactly one tag key" })
  const tag = keys[0]!
  const body = expr[tag]

  // Structural-only validation. Typechecking is separate.
  switch (tag) {
    case "lit":
      if (!isObject(body)) errors.push({ path, message: "lit must be object" })
      break
    case "var":
      if (!isObject(body)) errors.push({ path, message: "var must be object" })
      break
    case "get":
    case "has":
      if (!isObject(body) || body.expr == null || typeof body.path !== "string") errors.push({ path, message: `${tag} requires {expr,path}` })
      else validateExpr(errors, `${path}.${tag}.expr`, body.expr)
      break
    case "obj":
      if (!isObject(body) || !isObject(body.fields)) errors.push({ path, message: "obj requires {fields}" })
      else for (const [k, v] of Object.entries(body.fields)) validateExpr(errors, `${path}.obj.fields.${k}`, v)
      break
    case "arr":
      if (!isObject(body) || !Array.isArray(body.items)) errors.push({ path, message: "arr requires {items[]}" })
      else body.items.forEach((e: any, i: number) => validateExpr(errors, `${path}.arr.items[${i}]`, e))
      break

    case "not":
    case "bool":
    case "is_null":
      validateExpr(errors, `${path}.${tag}`, body)
      break

    case "and":
    case "or":
    case "coalesce":
      if (!Array.isArray(body)) errors.push({ path, message: `${tag} requires array` })
      else body.forEach((e: any, i: number) => validateExpr(errors, `${path}.${tag}[${i}]`, e))
      break

    case "eq":
    case "ne":
    case "lt":
    case "le":
    case "gt":
    case "ge":
    case "add":
    case "sub":
    case "mul":
    case "div":
    case "time_between":
      if (!Array.isArray(body) || body.length !== 2) errors.push({ path, message: `${tag} requires [a,b]` })
      else {
        validateExpr(errors, `${path}.${tag}[0]`, body[0])
        validateExpr(errors, `${path}.${tag}[1]`, body[1])
      }
      break

    case "in":
      if (!isObject(body) || body.needle == null || body.haystack == null) errors.push({ path, message: "in requires {needle,haystack}" })
      else {
        validateExpr(errors, `${path}.in.needle`, body.needle)
        validateExpr(errors, `${path}.in.haystack`, body.haystack)
      }
      break

    case "if":
      if (!isObject(body) || body.cond == null || body.then == null || body.else == null) errors.push({ path, message: "if requires {cond,then,else}" })
      else {
        validateExpr(errors, `${path}.if.cond`, body.cond)
        validateExpr(errors, `${path}.if.then`, body.then)
        validateExpr(errors, `${path}.if.else`, body.else)
      }
      break

    case "map_enum":
      if (!isObject(body) || body.expr == null || !isObject(body.mapping)) errors.push({ path, message: "map_enum requires {expr,mapping}" })
      else validateExpr(errors, `${path}.map_enum.expr`, body.expr)
      break

    case "call":
      if (!isObject(body) || typeof body.fn !== "string" || !Array.isArray(body.args)) errors.push({ path, message: "call requires {fn,args[]}" })
      else body.args.forEach((e: any, i: number) => validateExpr(errors, `${path}.call.args[${i}]`, e))
      break

    case "exists":
      if (!isObject(body) || !isObject(body.query)) errors.push({ path, message: "exists requires {query}" })
      break

    default:
      errors.push({ path, message: `unknown expr tag: ${tag}` })
  }
}

function validateWebhook (errors: ValidationError[], path: string, name: string, spec: any) {
  if (!isObject(spec)) {
    errors.push({ path, message: "webhook spec must be an object" })
    return
  }
  if (typeof spec.on_type !== "string") errors.push({ path: `${path}.on_type`, message: "on_type must be a string" })
  if (typeof spec.command !== "string") errors.push({ path: `${path}.command`, message: "command must be a string" })
  if (spec.queue !== undefined && typeof spec.queue !== "string") errors.push({ path: `${path}.queue`, message: "queue must be a string" })
  if (spec.routing !== undefined) validateExpr(errors, `${path}.routing`, spec.routing)
}

function isObject (x: unknown): x is Record<string, unknown> {
  return typeof x === "object" && x !== null && !Array.isArray(x)
}

function fail (errors: ValidationError[], path: string, message: string) {
  errors.push({ path, message })
  return { ok: false as const, errors }
}

function validateQueue (errors: ValidationError[], path: string, queueName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "queue spec must be an object" })

  if (!isObject(spec.message_type)) {
    errors.push({ path: `${path}.message_type`, message: "message_type must be an object" })
  }

  if (spec.ordering != null && !["unordered", "fifo", "per_key"].includes(spec.ordering)) {
    errors.push({ path: `${path}.ordering`, message: "invalid ordering" })
  }

  if (!isObject(spec.retention)) {
    errors.push({ path: `${path}.retention`, message: "retention must be an object" })
  } else {
    if (typeof spec.retention.max_age_seconds !== "number") {
      errors.push({ path: `${path}.retention.max_age_seconds`, message: "max_age_seconds must be a number" })
    }
  }

  if (!isObject(spec.delivery)) {
    errors.push({ path: `${path}.delivery`, message: "delivery must be an object" })
  } else {
    if (typeof spec.delivery.max_attempts !== "number") errors.push({ path: `${path}.delivery.max_attempts`, message: "max_attempts must be number" })
    if (typeof spec.delivery.initial_backoff_ms !== "number") errors.push({ path: `${path}.delivery.initial_backoff_ms`, message: "initial_backoff_ms must be number" })
    if (typeof spec.delivery.max_backoff_ms !== "number") errors.push({ path: `${path}.delivery.max_backoff_ms`, message: "max_backoff_ms must be number" })
  }

  if (spec.map_to != null) {
    if (!isObject(spec.map_to)) errors.push({ path: `${path}.map_to`, message: "map_to must be an object" })
    else {
      if (typeof spec.map_to.entity_type !== "string") errors.push({ path: `${path}.map_to.entity_type`, message: "entity_type must be string" })
      if (typeof spec.map_to.command !== "string") errors.push({ path: `${path}.map_to.command`, message: "command must be string" })
      if (!isObject(spec.map_to.input_map)) errors.push({ path: `${path}.map_to.input_map`, message: "input_map must be an object" })
    }
  }
}


function validateSla (errors: ValidationError[], path: string, slaName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "sla spec must be an object" })

  if (typeof spec.name !== "string") errors.push({ path: `${path}.name`, message: "name must be a string" })
  if (spec.name !== slaName) errors.push({ path: `${path}.name`, message: "name must match key" })

  if (typeof spec.on_type !== "string") errors.push({ path: `${path}.on_type`, message: "on_type must be a string" })

  if (!isObject(spec.start)) errors.push({ path: `${path}.start`, message: "start must be an object" })
  else {
    if (!isObject(spec.start.event)) errors.push({ path: `${path}.start.event`, message: "start.event must be an object" })
    else {
      if (typeof spec.start.event.name !== "string") errors.push({ path: `${path}.start.event.name`, message: "start.event.name must be a string" })
      if (spec.start.event.occurrence !== undefined && spec.start.event.occurrence !== "first") {
        errors.push({ path: `${path}.start.event.occurrence`, message: "start.event.occurrence must be first or undefined" })
      }
      if (spec.start.event.where !== undefined) validateExpr(errors, `${path}.start.event.where`, spec.start.event.where)
    }
  }

  if (!isObject(spec.stop)) errors.push({ path: `${path}.stop`, message: "stop must be an object" })
  else {
    if (!isObject(spec.stop.event)) errors.push({ path: `${path}.stop.event`, message: "stop.event must be an object" })
    else {
      if (typeof spec.stop.event.name !== "string") errors.push({ path: `${path}.stop.event.name`, message: "stop.event.name must be a string" })
      if (spec.stop.event.occurrence !== undefined && spec.stop.event.occurrence !== "first") {
        errors.push({ path: `${path}.stop.event.occurrence`, message: "stop.event.occurrence must be first or undefined" })
      }
      if (spec.stop.event.where !== undefined) validateExpr(errors, `${path}.stop.event.where`, spec.stop.event.where)
    }
  }

  if (typeof spec.within_seconds !== "number") errors.push({ path: `${path}.within_seconds`, message: "within_seconds must be a number" })

  if (!isObject(spec.enforce)) errors.push({ path: `${path}.enforce`, message: "enforce must be an object" })
  else {
    const enforceKeys = Object.keys(spec.enforce);
    if (enforceKeys.length !== 1) errors.push({ path: `${path}.enforce`, message: "enforce must have exactly one key" })
    else {
      const enforceType = enforceKeys[0];
      switch (enforceType) {
        case "none":
          if (spec.enforce.none !== true) errors.push({ path: `${path}.enforce.none`, message: "enforce.none must be true" })
          break
        case "notify":
          if (!isObject(spec.enforce.notify)) errors.push({ path: `${path}.enforce.notify`, message: "enforce.notify must be an object" })
          else {
            if (typeof spec.enforce.notify.emit_event !== "string") errors.push({ path: `${path}.enforce.notify.emit_event`, message: "enforce.notify.emit_event must be a string" })
            if (!isObject(spec.enforce.notify.payload)) errors.push({ path: `${path}.enforce.notify.payload`, message: "enforce.notify.payload must be an object" })
            else {
              for (const [k, v] of Object.entries(spec.enforce.notify.payload)) {
                validateExpr(errors, `${path}.enforce.notify.payload.${k}`, v)
              }
            }
          }
          break
        case "auto_transition":
          if (!isObject(spec.enforce.auto_transition)) errors.push({ path: `${path}.enforce.auto_transition`, message: "enforce.auto_transition must be an object" })
          else {
            if (typeof spec.enforce.auto_transition.to_state !== "string") errors.push({ path: `${path}.enforce.auto_transition.to_state`, message: "enforce.auto_transition.to_state must be a string" })
          }
          break
        default:
          errors.push({ path: `${path}.enforce`, message: `unknown enforce type: ${enforceType}` })
      }
    }
  }
}
function validateSchedule (errors: ValidationError[], path: string, schedName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "schedule spec must be an object" })

  if (typeof spec.name !== "string") errors.push({ path: `${path}.name`, message: "name must be a string" })
  if (spec.name !== schedName) errors.push({ path: `${path}.name`, message: "name must match key" })

  if (!isObject(spec.trigger)) errors.push({ path: `${path}.trigger`, message: "trigger must be an object" })
  else {
    const triggerKeys = Object.keys(spec.trigger);
    if (triggerKeys.length !== 1) errors.push({ path: `${path}.trigger`, message: "trigger must have exactly one key" })
    else {
      const triggerType = triggerKeys[0];
      switch (triggerType) {
        case "cron":
          if (!isObject(spec.trigger.cron)) errors.push({ path: `${path}.trigger.cron`, message: "cron trigger must be an object" })
          else {
            if (typeof spec.trigger.cron.expression !== "string") errors.push({ path: `${path}.trigger.cron.expression`, message: "cron.expression must be a string" })
            if (spec.trigger.cron.timezone !== undefined && typeof spec.trigger.cron.timezone !== "string") errors.push({ path: `${path}.trigger.cron.timezone`, message: "cron.timezone must be a string" })
          }
          break
        case "delay":
          if (typeof spec.trigger.delay !== "number") errors.push({ path: `${path}.trigger.delay`, message: "delay trigger must be a number" })
          break
        case "event":
          if (!isObject(spec.trigger.event)) errors.push({ path: `${path}.trigger.event`, message: "event trigger must be an object" })
          else {
            if (typeof spec.trigger.event.on_type !== "string") errors.push({ path: `${path}.trigger.event.on_type`, message: "event.on_type must be a string" })
            if (typeof spec.trigger.event.event_type !== "string") errors.push({ path: `${path}.trigger.event.event_type`, message: "event.event_type must be a string" })
            if (spec.trigger.event.where !== undefined) validateExpr(errors, `${path}.trigger.event.where`, spec.trigger.event.where)
          }
          break
        default:
          errors.push({ path: `${path}.trigger`, message: `unknown trigger type: ${triggerType}` })
      }
    }
  }

  if (!isObject(spec.action)) errors.push({ path: `${path}.action`, message: "action must be an object" })
  else {
    if (!isObject(spec.action.target)) errors.push({ path: `${path}.action.target`, message: "action.target must be an object" })
    else {
      const targetKeys = Object.keys(spec.action.target);
      if (targetKeys.length !== 1) errors.push({ path: `${path}.action.target`, message: "action.target must have exactly one key" })
      else {
        const targetType = targetKeys[0];
        switch (targetType) {
          case "command":
            if (!isObject(spec.action.target.command)) errors.push({ path: `${path}.action.target.command`, message: "command target must be an object" })
            else {
              if (typeof spec.action.target.command.entity_type !== "string") errors.push({ path: `${path}.action.target.command.entity_type`, message: "command.entity_type must be a string" })
              if (typeof spec.action.target.command.command_name !== "string") errors.push({ path: `${path}.action.target.command.command_name`, message: "command.command_name must be a string" })
              if (spec.action.target.command.entity_id_expr !== undefined) validateExpr(errors, `${path}.action.target.command.entity_id_expr`, spec.action.target.command.entity_id_expr)
            }
            break
          case "webhook":
            if (!isObject(spec.action.target.webhook)) errors.push({ path: `${path}.action.target.webhook`, message: "webhook target must be an object" })
            else {
              if (typeof spec.action.target.webhook.url !== "string") errors.push({ path: `${path}.action.target.webhook.url`, message: "webhook.url must be a string" })
              if (spec.action.target.webhook.method !== undefined && typeof spec.action.target.webhook.method !== "string") errors.push({ path: `${path}.action.target.webhook.method`, message: "webhook.method must be a string" })
            }
            break
          case "queue":
            if (!isObject(spec.action.target.queue)) errors.push({ path: `${path}.action.target.queue`, message: "queue target must be an object" })
            else {
              if (typeof spec.action.target.queue.name !== "string") errors.push({ path: `${path}.action.target.queue.name`, message: "queue.name must be a string" })
            }
            break
          default:
            errors.push({ path: `${path}.action.target`, message: `unknown target type: ${targetType}` })
        }
      }
    }

    if (spec.action.input_map !== undefined) {
      if (!isObject(spec.action.input_map)) errors.push({ path: `${path}.action.input_map`, message: "action.input_map must be an object" })
      else {
        for (const [k, v] of Object.entries(spec.action.input_map)) {
          validateExpr(errors, `${path}.action.input_map.${k}`, v)
        }
      }
    }

    if (spec.action.retry_policy !== undefined) {
      validateRetryPolicy(errors, `${path}.action.retry_policy`, spec.action.retry_policy)
    }
  }

  if (spec.enabled !== undefined && typeof spec.enabled !== "boolean") errors.push({ path: `${path}.enabled`, message: "enabled must be a boolean" })
  if (spec.metadata !== undefined && !isObject(spec.metadata)) errors.push({ path: `${path}.metadata`, message: "metadata must be an object" })
}

function validateWorkflow (errors: ValidationError[], path: string, wfName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "workflow spec must be an object" })

  if (typeof spec.name !== "string") errors.push({ path: `${path}.name`, message: "name must be a string" })
  if (spec.name !== wfName) errors.push({ path: `${path}.name`, message: "name must match key" })

  if (typeof spec.start_step !== "string") errors.push({ path: `${path}.start_step`, message: "start_step must be a string" })

  if (!isObject(spec.steps)) errors.push({ path: `${path}.steps`, message: "steps must be an object" })
  else {
    for (const [stepName, stepSpec] of Object.entries(spec.steps)) {
      validateWorkflowStep(errors, `${path}.steps.${stepName}`, stepName, stepSpec)
    }
  }

  if (spec.compensation !== undefined) {
    validateWorkflowCompensation(errors, `${path}.compensation`, spec.compensation)
  }

  if (spec.metadata !== undefined && !isObject(spec.metadata)) errors.push({ path: `${path}.metadata`, message: "metadata must be an object" })
}

function validateWorkflowStep (errors: ValidationError[], path: string, stepName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "workflow step must be an object" })

  const stepKeys = Object.keys(spec);
  if (stepKeys.length !== 1) errors.push({ path, message: "workflow step must have exactly one key" })
  else {
    const stepType = stepKeys[0];
    switch (stepType) {
      case "command":
        if (!isObject(spec.command)) errors.push({ path: `${path}.command`, message: "command step must be an object" })
        else {
          // Validate command step
          if (!isObject(spec.command.target)) errors.push({ path: `${path}.command.target`, message: "command.target must be an object" })
          else {
            const targetKeys = Object.keys(spec.command.target);
            if (targetKeys.length !== 1) errors.push({ path: `${path}.command.target`, message: "command.target must have exactly one key" })
            else {
              const targetType = targetKeys[0];
              switch (targetType) {
                case "command":
                  if (!isObject(spec.command.target.command)) errors.push({ path: `${path}.command.target.command`, message: "command target must be an object" })
                  else {
                    if (typeof spec.command.target.command.entity_type !== "string") errors.push({ path: `${path}.command.target.command.entity_type`, message: "command.entity_type must be a string" })
                    if (typeof spec.command.target.command.command_name !== "string") errors.push({ path: `${path}.command.target.command.command_name`, message: "command.command_name must be a string" })
                    if (spec.command.target.command.entity_id_expr !== undefined) validateExpr(errors, `${path}.command.target.command.entity_id_expr`, spec.command.target.command.entity_id_expr)
                  }
                  break
                case "webhook":
                  if (!isObject(spec.command.target.webhook)) errors.push({ path: `${path}.command.target.webhook`, message: "webhook target must be an object" })
                  else {
                    if (typeof spec.command.target.webhook.url !== "string") errors.push({ path: `${path}.command.target.webhook.url`, message: "webhook.url must be a string" })
                    if (spec.command.target.webhook.method !== undefined && typeof spec.command.target.webhook.method !== "string") errors.push({ path: `${path}.command.target.webhook.method`, message: "webhook.method must be a string" })
                  }
                  break
                case "queue":
                  if (!isObject(spec.command.target.queue)) errors.push({ path: `${path}.command.target.queue`, message: "queue target must be an object" })
                  else {
                    if (typeof spec.command.target.queue.name !== "string") errors.push({ path: `${path}.command.target.queue.name`, message: "queue.name must be a string" })
                  }
                  break
                default:
                  errors.push({ path: `${path}.command.target`, message: `unknown target type: ${targetType}` })
              }
            }
          }

          if (spec.command.input_map !== undefined) {
            if (!isObject(spec.command.input_map)) errors.push({ path: `${path}.command.input_map`, message: "command.input_map must be an object" })
            else {
              for (const [k, v] of Object.entries(spec.command.input_map)) {
                validateExpr(errors, `${path}.command.input_map.${k}`, v)
              }
            }
          }

          if (spec.command.on_success !== undefined && typeof spec.command.on_success !== "string") errors.push({ path: `${path}.command.on_success`, message: "command.on_success must be a string" })
          if (spec.command.on_failure !== undefined && typeof spec.command.on_failure !== "string") errors.push({ path: `${path}.command.on_failure`, message: "command.on_failure must be a string" })

          if (spec.command.retry_policy !== undefined) {
            validateRetryPolicy(errors, `${path}.command.retry_policy`, spec.command.retry_policy)
          }
        }
        break
      case "wait":
        if (!isObject(spec.wait)) errors.push({ path: `${path}.wait`, message: "wait step must be an object" })
        else {
          if (spec.wait.timeout_seconds !== undefined && typeof spec.wait.timeout_seconds !== "number") errors.push({ path: `${path}.wait.timeout_seconds`, message: "wait.timeout_seconds must be a number" })
          
          if (spec.wait.wait_for_event !== undefined) {
            if (!isObject(spec.wait.wait_for_event)) errors.push({ path: `${path}.wait.wait_for_event`, message: "wait.wait_for_event must be an object" })
            else {
              if (typeof spec.wait.wait_for_event.on_type !== "string") errors.push({ path: `${path}.wait.wait_for_event.on_type`, message: "wait.wait_for_event.on_type must be a string" })
              if (typeof spec.wait.wait_for_event.event_type !== "string") errors.push({ path: `${path}.wait.wait_for_event.event_type`, message: "wait.wait_for_event.event_type must be a string" })
              if (spec.wait.wait_for_event.where !== undefined) validateExpr(errors, `${path}.wait.wait_for_event.where`, spec.wait.wait_for_event.where)
            }
          }

          if (spec.wait.on_timeout !== undefined && typeof spec.wait.on_timeout !== "string") errors.push({ path: `${path}.wait.on_timeout`, message: "wait.on_timeout must be a string" })
          if (spec.wait.on_event !== undefined && typeof spec.wait.on_event !== "string") errors.push({ path: `${path}.wait.on_event`, message: "wait.on_event must be a string" })
        }
        break
      case "decision":
        if (!isObject(spec.decision)) errors.push({ path: `${path}.decision`, message: "decision step must be an object" })
        else {
          validateExpr(errors, `${path}.decision.condition`, spec.decision.condition)
          if (typeof spec.decision.on_true !== "string") errors.push({ path: `${path}.decision.on_true`, message: "decision.on_true must be a string" })
          if (typeof spec.decision.on_false !== "string") errors.push({ path: `${path}.decision.on_false`, message: "decision.on_false must be a string" })
        }
        break
      case "parallel":
        if (!isObject(spec.parallel)) errors.push({ path: `${path}.parallel`, message: "parallel step must be an object" })
        else {
          if (!isObject(spec.parallel.branches)) errors.push({ path: `${path}.parallel.branches`, message: "parallel.branches must be an object" })
          else {
            for (const [branchName, branchSpec] of Object.entries(spec.parallel.branches)) {
              validateWorkflowStep(errors, `${path}.parallel.branches.${branchName}`, branchName, branchSpec)
            }
          }

          if (typeof spec.parallel.on_completion !== "string") errors.push({ path: `${path}.parallel.on_completion`, message: "parallel.on_completion must be a string" })
          if (spec.parallel.on_failure !== undefined && typeof spec.parallel.on_failure !== "string") errors.push({ path: `${path}.parallel.on_failure`, message: "parallel.on_failure must be a string" })
        }
        break
      default:
        errors.push({ path, message: `unknown step type: ${stepType}` })
    }
  }
}

function validateWorkflowCompensation (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "workflow compensation must be an object" })

  if (typeof spec.strategy !== "string" || !["saga", "reverse-order", "custom"].includes(spec.strategy)) {
    errors.push({ path: `${path}.strategy`, message: "compensation.strategy must be 'saga', 'reverse-order', or 'custom'" })
  }

  if (spec.custom_steps !== undefined) {
    if (!isObject(spec.custom_steps)) errors.push({ path: `${path}.custom_steps`, message: "compensation.custom_steps must be an object" })
    else {
      for (const [stepName, stepSpec] of Object.entries(spec.custom_steps)) {
        validateWorkflowStep(errors, `${path}.compensation.custom_steps.${stepName}`, stepName, stepSpec)
      }
    }
  }
}

function validateRetryPolicy (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "retry policy must be an object" })

  if (typeof spec.max_attempts !== "number") errors.push({ path: `${path}.max_attempts`, message: "max_attempts must be a number" })

  if (!isObject(spec.backoff)) errors.push({ path: `${path}.backoff`, message: "retry.backoff must be an object" })
  else {
    if (typeof spec.backoff.initial_delay_ms !== "number") errors.push({ path: `${path}.backoff.initial_delay_ms`, message: "backoff.initial_delay_ms must be a number" })
    if (typeof spec.backoff.max_delay_ms !== "number") errors.push({ path: `${path}.backoff.max_delay_ms`, message: "backoff.max_delay_ms must be a number" })
    if (typeof spec.backoff.multiplier !== "number") errors.push({ path: `${path}.backoff.multiplier`, message: "backoff.multiplier must be a number" })
  }
}

function validateMultiEntityCommand (errors: ValidationError[], path: string, commandName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "multi-entity command spec must be an object" })

  if (typeof spec.name !== "string") errors.push({ path: `${path}.name`, message: "name must be a string" })
  if (spec.name !== commandName) errors.push({ path: `${path}.name`, message: "name must match key" })

  if (!Array.isArray(spec.steps)) errors.push({ path: `${path}.steps`, message: "steps must be an array" })
  else {
    for (let i = 0; i < spec.steps.length; i++) {
      validateMultiEntityCommandStep(errors, `${path}.steps[${i}]`, spec.steps[i])
    }
  }

  if (!isObject(spec.transaction_boundary)) errors.push({ path: `${path}.transaction_boundary`, message: "transaction_boundary must be an object" })
  else {
    const tb = spec.transaction_boundary;
    if (typeof tb.kind !== "string" || !["atomic", "compensatable", "best_effort"].includes(tb.kind)) {
      errors.push({ path: `${path}.transaction_boundary.kind`, message: "transaction_boundary.kind must be 'atomic', 'compensatable', or 'best_effort'" })
    }
    
    if (tb.isolation_level !== undefined && !["read_uncommitted", "read_committed", "repeatable_read", "serializable"].includes(tb.isolation_level)) {
      errors.push({ path: `${path}.transaction_boundary.isolation_level`, message: "transaction_boundary.isolation_level must be a valid isolation level" })
    }
  }

  if (spec.compensation_strategy !== undefined) {
    validateCompensationStrategy(errors, `${path}.compensation_strategy`, spec.compensation_strategy)
  }

  if (!isObject(spec.partial_failure_handling)) errors.push({ path: `${path}.partial_failure_handling`, message: "partial_failure_handling must be an object" })
  else {
    const pfh = spec.partial_failure_handling;
    if (typeof pfh.strategy !== "string" || !["fail_fast", "continue_and_compensate", "partial_commit"].includes(pfh.strategy)) {
      errors.push({ path: `${path}.partial_failure_handling.strategy`, message: "partial_failure_handling.strategy must be 'fail_fast', 'continue_and_compensate', or 'partial_commit'" })
    }
    
    if (pfh.on_failure !== undefined && !["compensate_all", "compensate_partial", "manual_intervention"].includes(pfh.on_failure)) {
      errors.push({ path: `${path}.partial_failure_handling.on_failure`, message: "partial_failure_handling.on_failure must be a valid option" })
    }
  }
}

function validateMultiEntityCommandStep (errors: ValidationError[], path: string, step: any) {
  if (!isObject(step)) return void errors.push({ path, message: "command step must be an object" })

  const stepKeys = Object.keys(step);
  if (stepKeys.length !== 1) errors.push({ path, message: "command step must have exactly one key" })
  else {
    const stepType = stepKeys[0];
    switch (stepType) {
      case "command":
        if (!isObject(step.command)) errors.push({ path: `${path}.command`, message: "command step must be an object" })
        else {
          if (typeof step.command.entity_type !== "string") errors.push({ path: `${path}.command.entity_type`, message: "command.entity_type must be a string" })
          if (typeof step.command.command_name !== "string") errors.push({ path: `${path}.command.command_name`, message: "command.command_name must be a string" })
          if (step.command.entity_id_expr !== undefined) validateExpr(errors, `${path}.command.entity_id_expr`, step.command.entity_id_expr)
          
          if (!isObject(step.command.input)) errors.push({ path: `${path}.command.input`, message: "command.input must be an object" })
          else {
            for (const [k, v] of Object.entries(step.command.input)) {
              validateExpr(errors, `${path}.command.input.${k}`, v)
            }
          }
        }
        break
      case "wait":
        if (!isObject(step.wait)) errors.push({ path: `${path}.wait`, message: "wait step must be an object" })
        else {
          if (typeof step.wait.duration_ms !== "number") errors.push({ path: `${path}.wait.duration_ms`, message: "wait.duration_ms must be a number" })
        }
        break
      case "condition":
        if (!isObject(step.condition)) errors.push({ path: `${path}.condition`, message: "condition step must be an object" })
        else {
          validateExpr(errors, `${path}.condition.expr`, step.condition.expr)
          
          if (!Array.isArray(step.condition.then_steps)) errors.push({ path: `${path}.condition.then_steps`, message: "condition.then_steps must be an array" })
          else {
            for (let i = 0; i < step.condition.then_steps.length; i++) {
              validateMultiEntityCommandStep(errors, `${path}.condition.then_steps[${i}]`, step.condition.then_steps[i])
            }
          }
          
          if (step.condition.else_steps !== undefined) {
            if (!Array.isArray(step.condition.else_steps)) errors.push({ path: `${path}.condition.else_steps`, message: "condition.else_steps must be an array" })
            else {
              for (let i = 0; i < step.condition.else_steps.length; i++) {
                validateMultiEntityCommandStep(errors, `${path}.condition.else_steps[${i}]`, step.condition.else_steps[i])
              }
            }
          }
        }
        break
      default:
        errors.push({ path, message: `unknown step type: ${stepType}` })
    }
  }
}

function validateCompensationStrategy (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "compensation strategy must be an object" })

  if (typeof spec.strategy !== "string" || !["saga", "rollback", "manual"].includes(spec.strategy)) {
    errors.push({ path: `${path}.strategy`, message: "compensation.strategy must be 'saga', 'rollback', or 'manual'" })
  }

  if (spec.saga_steps !== undefined) {
    if (!Array.isArray(spec.saga_steps)) errors.push({ path: `${path}.saga_steps`, message: "compensation.saga_steps must be an array" })
    else {
      for (let i = 0; i < spec.saga_steps.length; i++) {
        validateCompensationStep(errors, `${path}.saga_steps[${i}]`, spec.saga_steps[i])
      }
    }
  }
}

function validateCompensationStep (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "compensation step must be an object" })

  if (typeof spec.entity_type !== "string") errors.push({ path: `${path}.entity_type`, message: "entity_type must be a string" })
  if (typeof spec.command_name !== "string") errors.push({ path: `${path}.command_name`, message: "command_name must be a string" })
  validateExpr(errors, `${path}.entity_id_expr`, spec.entity_id_expr)
  
  if (!isObject(spec.input)) errors.push({ path: `${path}.input`, message: "input must be an object" })
  else {
    for (const [k, v] of Object.entries(spec.input)) {
      validateExpr(errors, `${path}.input.${k}`, v)
    }
  }
}

function validateUiSpec (errors: ValidationError[], path: string, uiName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "ui spec must be an object" })

  if (spec.screens !== undefined) {
    if (!isObject(spec.screens)) errors.push({ path: `${path}.screens`, message: "screens must be an object" })
    else {
      for (const [screenName, screenSpec] of Object.entries(spec.screens)) {
        validateScreenSpec(errors, `${path}.screens.${screenName}`, screenName, screenSpec)
      }
    }
  }

  if (spec.dashboards !== undefined) {
    if (!isObject(spec.dashboards)) errors.push({ path: `${path}.dashboards`, message: "dashboards must be an object" })
    else {
      for (const [dashboardName, dashboardSpec] of Object.entries(spec.dashboards)) {
        validateDashboardSpec(errors, `${path}.dashboards.${dashboardName}`, dashboardName, dashboardSpec)
      }
    }
  }

  if (spec.navigation !== undefined) {
    validateNavigationSpec(errors, `${path}.navigation`, spec.navigation)
  }

  if (spec.themes !== undefined) {
    if (!isObject(spec.themes)) errors.push({ path: `${path}.themes`, message: "themes must be an object" })
    else {
      for (const [themeName, themeSpec] of Object.entries(spec.themes)) {
        validateThemeSpec(errors, `${path}.themes.${themeName}`, themeName, themeSpec)
      }
    }
  }
}

function validateScreenSpec (errors: ValidationError[], path: string, screenName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "screen spec must be an object" })

  if (typeof spec.title !== "string") errors.push({ path: `${path}.title`, message: "title must be a string" })

  if (!isObject(spec.layout)) errors.push({ path: `${path}.layout`, message: "layout must be an object" })
  else validateLayoutSpec(errors, `${path}.layout`, spec.layout)

  if (!isObject(spec.data_source)) errors.push({ path: `${path}.data_source`, message: "data_source must be an object" })
  else validateDataSourceSpec(errors, `${path}.data_source`, spec.data_source)

  if (spec.permissions !== undefined) {
    validatePermissionSpec(errors, `${path}.permissions`, spec.permissions)
  }
}

function validateDashboardSpec (errors: ValidationError[], path: string, dashboardName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "dashboard spec must be an object" })

  if (typeof spec.title !== "string") errors.push({ path: `${path}.title`, message: "title must be a string" })

  if (!Array.isArray(spec.widgets)) errors.push({ path: `${path}.widgets`, message: "widgets must be an array" })
  else {
    for (let i = 0; i < spec.widgets.length; i++) {
      validateWidgetSpec(errors, `${path}.widgets[${i}]`, spec.widgets[i])
    }
  }

  if (!isObject(spec.layout)) errors.push({ path: `${path}.layout`, message: "layout must be an object" })
  else validateLayoutSpec(errors, `${path}.layout`, spec.layout)

  if (spec.permissions !== undefined) {
    validatePermissionSpec(errors, `${path}.permissions`, spec.permissions)
  }
}

function validateNavigationSpec (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "navigation spec must be an object" })

  if (!Array.isArray(spec.sections)) errors.push({ path: `${path}.sections`, message: "sections must be an array" })
  else {
    for (let i = 0; i < spec.sections.length; i++) {
      validateNavigationSection(errors, `${path}.sections[${i}]`, spec.sections[i])
    }
  }
}

function validateNavigationSection (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "navigation section must be an object" })

  if (typeof spec.id !== "string") errors.push({ path: `${path}.id`, message: "id must be a string" })
  if (typeof spec.title !== "string") errors.push({ path: `${path}.title`, message: "title must be a string" })

  if (!Array.isArray(spec.items)) errors.push({ path: `${path}.items`, message: "items must be an array" })
  else {
    for (let i = 0; i < spec.items.length; i++) {
      validateNavigationItem(errors, `${path}.items[${i}]`, spec.items[i])
    }
  }

  if (spec.permissions !== undefined) {
    validatePermissionSpec(errors, `${path}.permissions`, spec.permissions)
  }
}

function validateNavigationItem (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "navigation item must be an object" })

  if (typeof spec.id !== "string") errors.push({ path: `${path}.id`, message: "id must be a string" })
  if (typeof spec.title !== "string") errors.push({ path: `${path}.title`, message: "title must be a string" })
  if (typeof spec.route !== "string") errors.push({ path: `${path}.route`, message: "route must be a string" })

  if (spec.permissions !== undefined) {
    validatePermissionSpec(errors, `${path}.permissions`, spec.permissions)
  }
}

function validateLayoutSpec (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "layout spec must be an object" })

  const layoutTypes = ["grid", "form", "table", "tabs", "sidebar"];
  const specKeys = Object.keys(spec);
  if (specKeys.length !== 1) errors.push({ path, message: "layout spec must have exactly one kind" })
  else {
    const kind = specKeys[0];
    if (!layoutTypes.includes(kind)) {
      errors.push({ path, message: `layout kind must be one of: ${layoutTypes.join(', ')}` })
    } else {
      switch (kind) {
        case "grid":
          if (typeof spec.grid.columns !== "number") errors.push({ path: `${path}.grid.columns`, message: "columns must be a number" })
          if (!Array.isArray(spec.grid.items)) errors.push({ path: `${path}.grid.items`, message: "items must be an array" })
          else {
            for (let i = 0; i < spec.grid.items.length; i++) {
              validateLayoutItem(errors, `${path}.grid.items[${i}]`, spec.grid.items[i])
            }
          }
          break;
        case "form":
          if (!Array.isArray(spec.form.fields)) errors.push({ path: `${path}.form.fields`, message: "fields must be an array" })
          else {
            for (let i = 0; i < spec.form.fields.length; i++) {
              validateFormField(errors, `${path}.form.fields[${i}]`, spec.form.fields[i])
            }
          }
          break;
        case "table":
          if (!Array.isArray(spec.table.columns)) errors.push({ path: `${path}.table.columns`, message: "columns must be an array" })
          else {
            for (let i = 0; i < spec.table.columns.length; i++) {
              validateTableColumn(errors, `${path}.table.columns[${i}]`, spec.table.columns[i])
            }
          }
          break;
        case "tabs":
          if (!Array.isArray(spec.tabs.tabs)) errors.push({ path: `${path}.tabs.tabs`, message: "tabs must be an array" })
          else {
            for (let i = 0; i < spec.tabs.tabs.length; i++) {
              validateTabSpec(errors, `${path}.tabs.tabs[${i}]`, spec.tabs.tabs[i])
            }
          }
          break;
        case "sidebar":
          if (!isObject(spec.sidebar.main)) errors.push({ path: `${path}.sidebar.main`, message: "main layout must be an object" })
          else validateLayoutSpec(errors, `${path}.sidebar.main`, spec.sidebar.main)
          if (!isObject(spec.sidebar.sidebar)) errors.push({ path: `${path}.sidebar.sidebar`, message: "sidebar layout must be an object" })
          else validateLayoutSpec(errors, `${path}.sidebar.sidebar`, spec.sidebar.sidebar)
          break;
      }
    }
  }
}

function validateLayoutItem (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "layout item must be an object" })

  if (typeof spec.component !== "string") errors.push({ path: `${path}.component`, message: "component must be a string" })

  if (spec.props !== undefined) {
    if (!isObject(spec.props)) errors.push({ path: `${path}.props`, message: "props must be an object" })
    else {
      for (const [k, v] of Object.entries(spec.props)) {
        validateExpr(errors, `${path}.props.${k}`, v)
      }
    }
  }

  if (spec.col_span !== undefined && typeof spec.col_span !== "number") errors.push({ path: `${path}.col_span`, message: "col_span must be a number" })
  if (spec.row_span !== undefined && typeof spec.row_span !== "number") errors.push({ path: `${path}.row_span`, message: "row_span must be a number" })
}

function validateFormField (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "form field must be an object" })

  if (typeof spec.name !== "string") errors.push({ path: `${path}.name`, message: "name must be a string" })
  if (typeof spec.label !== "string") errors.push({ path: `${path}.label`, message: "label must be a string" })

  const validTypes = ["text", "number", "boolean", "date", "select", "textarea", "file"];
  if (typeof spec.type !== "string" || !validTypes.includes(spec.type)) {
    errors.push({ path: `${path}.type`, message: `type must be one of: ${validTypes.join(', ')}` })
  }

  if (spec.required !== undefined && typeof spec.required !== "boolean") errors.push({ path: `${path}.required`, message: "required must be a boolean" })

  if (spec.validation !== undefined) validateExpr(errors, `${path}.validation`, spec.validation)
  if (spec.default_value !== undefined) validateExpr(errors, `${path}.default_value`, spec.default_value)
}

function validateTableColumn (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "table column must be an object" })

  if (typeof spec.name !== "string") errors.push({ path: `${path}.name`, message: "name must be a string" })
  if (typeof spec.label !== "string") errors.push({ path: `${path}.label`, message: "label must be a string" })

  const validTypes = ["text", "number", "boolean", "date", "link", "action"];
  if (typeof spec.type !== "string" || !validTypes.includes(spec.type)) {
    errors.push({ path: `${path}.type`, message: `type must be one of: ${validTypes.join(', ')}` })
  }

  if (spec.sortable !== undefined && typeof spec.sortable !== "boolean") errors.push({ path: `${path}.sortable`, message: "sortable must be a boolean" })
  if (spec.filterable !== undefined && typeof spec.filterable !== "boolean") errors.push({ path: `${path}.filterable`, message: "filterable must be a boolean" })
  if (spec.formatter !== undefined) validateExpr(errors, `${path}.formatter`, spec.formatter)
}

function validateTabSpec (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "tab spec must be an object" })

  if (typeof spec.id !== "string") errors.push({ path: `${path}.id`, message: "id must be a string" })
  if (typeof spec.title !== "string") errors.push({ path: `${path}.title`, message: "title must be a string" })

  if (!isObject(spec.content)) errors.push({ path: `${path}.content`, message: "content must be an object" })
  else validateLayoutSpec(errors, `${path}.content`, spec.content)
}

function validateWidgetSpec (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "widget spec must be an object" })

  if (typeof spec.id !== "string") errors.push({ path: `${path}.id`, message: "id must be a string" })
  if (typeof spec.title !== "string") errors.push({ path: `${path}.title`, message: "title must be a string" })

  const validTypes = ["metric", "chart", "table", "list", "form"];
  if (typeof spec.type !== "string" || !validTypes.includes(spec.type)) {
    errors.push({ path: `${path}.type`, message: `type must be one of: ${validTypes.join(', ')}` })
  }

  if (!isObject(spec.data_source)) errors.push({ path: `${path}.data_source`, message: "data_source must be an object" })
  else validateDataSourceSpec(errors, `${path}.data_source`, spec.data_source)

  if (spec.config !== undefined) {
    if (!isObject(spec.config)) errors.push({ path: `${path}.config`, message: "config must be an object" })
    else {
      for (const [k, v] of Object.entries(spec.config)) {
        validateExpr(errors, `${path}.config.${k}`, v)
      }
    }
  }
}

function validateDataSourceSpec (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "data source spec must be an object" })

  const dataSourceTypes = ["view", "entity", "api"];
  const specKeys = Object.keys(spec);
  if (specKeys.length !== 1) errors.push({ path, message: "data source spec must have exactly one kind" })
  else {
    const kind = specKeys[0];
    if (!dataSourceTypes.includes(kind)) {
      errors.push({ path, message: `data source kind must be one of: ${dataSourceTypes.join(', ')}` })
    } else {
      switch (kind) {
        case "view":
          if (typeof spec.view.view_name !== "string") errors.push({ path: `${path}.view.view_name`, message: "view_name must be a string" })
          if (spec.view.args !== undefined) {
            if (!isObject(spec.view.args)) errors.push({ path: `${path}.view.args`, message: "args must be an object" })
            else {
              for (const [k, v] of Object.entries(spec.view.args)) {
                validateExpr(errors, `${path}.view.args.${k}`, v)
              }
            }
          }
          break;
        case "entity":
          if (typeof spec.entity.entity_type !== "string") errors.push({ path: `${path}.entity.entity_type`, message: "entity_type must be a string" })
          if (spec.entity.query !== undefined) validateExpr(errors, `${path}.entity.query`, spec.entity.query)
          break;
        case "api":
          if (typeof spec.api.endpoint !== "string") errors.push({ path: `${path}.api.endpoint`, message: "endpoint must be a string" })
          if (spec.api.method !== undefined && typeof spec.api.method !== "string") errors.push({ path: `${path}.api.method`, message: "method must be a string" })
          if (spec.api.params !== undefined) {
            if (!isObject(spec.api.params)) errors.push({ path: `${path}.api.params`, message: "params must be an object" })
            else {
              for (const [k, v] of Object.entries(spec.api.params)) {
                validateExpr(errors, `${path}.api.params.${k}`, v)
              }
            }
          }
          break;
      }
    }
  }
}

function validatePermissionSpec (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "permission spec must be an object" })

  if (spec.roles !== undefined) {
    if (!Array.isArray(spec.roles)) errors.push({ path: `${path}.roles`, message: "roles must be an array" })
    else {
      for (let i = 0; i < spec.roles.length; i++) {
        if (typeof spec.roles[i] !== "string") errors.push({ path: `${path}.roles[${i}]`, message: "role must be a string" })
      }
    }
  }

  if (spec.conditions !== undefined) {
    if (!Array.isArray(spec.conditions)) errors.push({ path: `${path}.conditions`, message: "conditions must be an array" })
    else {
      for (let i = 0; i < spec.conditions.length; i++) {
        validateExpr(errors, `${path}.conditions[${i}]`, spec.conditions[i])
      }
    }
  }
}

function validateThemeSpec (errors: ValidationError[], path: string, themeName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "theme spec must be an object" })

  if (typeof spec.name !== "string") errors.push({ path: `${path}.name`, message: "name must be a string" })
  if (spec.name !== themeName) errors.push({ path: `${path}.name`, message: "name must match key" })

  const validModes = ["light", "dark", "auto"];
  if (typeof spec.mode !== "string" || !validModes.includes(spec.mode)) {
    errors.push({ path: `${path}.mode`, message: `mode must be one of: ${validModes.join(', ')}` })
  }

  if (spec.colors !== undefined && !isObject(spec.colors)) errors.push({ path: `${path}.colors`, message: "colors must be an object" })
  if (spec.spacing !== undefined && !isObject(spec.spacing)) errors.push({ path: `${path}.spacing`, message: "spacing must be an object" })

  if (spec.typography !== undefined) {
    validateTypographySpec(errors, `${path}.typography`, spec.typography)
  }
}

function validateTypographySpec (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "typography spec must be an object" })

  if (spec.font_family !== undefined && typeof spec.font_family !== "string") errors.push({ path: `${path}.font_family`, message: "font_family must be a string" })

  if (spec.sizes !== undefined && !isObject(spec.sizes)) errors.push({ path: `${path}.sizes`, message: "sizes must be an object" })
  if (spec.weights !== undefined && !isObject(spec.weights)) errors.push({ path: `${path}.weights`, message: "weights must be an object" })
}

function validateServiceSpec (errors: ValidationError[], path: string, serviceName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "service spec must be an object" })

  if (typeof spec.name !== "string") errors.push({ path: `${path}.name`, message: "name must be a string" })
  if (spec.name !== serviceName) errors.push({ path: `${path}.name`, message: "name must match key" })

  if (typeof spec.base_url !== "string") errors.push({ path: `${path}.base_url`, message: "base_url must be a string" })

  if (spec.auth !== undefined) {
    validateServiceAuth(errors, `${path}.auth`, spec.auth)
  }

  if (!isObject(spec.operations)) errors.push({ path: `${path}.operations`, message: "operations must be an object" })
  else {
    for (const [opName, opSpec] of Object.entries(spec.operations)) {
      validateOperationSpec(errors, `${path}.operations.${opName}`, opName, opSpec)
    }
  }

  if (spec.retry_policy !== undefined) {
    validateRetryPolicy(errors, `${path}.retry_policy`, spec.retry_policy)
  }

  if (spec.circuit_breaker !== undefined) {
    validateCircuitBreaker(errors, `${path}.circuit_breaker`, spec.circuit_breaker)
  }

  if (spec.timeout_ms !== undefined && typeof spec.timeout_ms !== "number") errors.push({ path: `${path}.timeout_ms`, message: "timeout_ms must be a number" })
}

function validateServiceAuth (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "service auth must be an object" })

  const authTypes = Object.keys(spec);
  if (authTypes.length !== 1) errors.push({ path, message: "service auth must have exactly one type" })
  else {
    const authType = authTypes[0];
    switch (authType) {
      case "api_key":
        if (typeof spec.api_key.header !== "string") errors.push({ path: `${path}.api_key.header`, message: "header must be a string" })
        if (typeof spec.api_key.env_var !== "string") errors.push({ path: `${path}.api_key.env_var`, message: "env_var must be a string" })
        break;
      case "basic":
        if (typeof spec.basic.username_env !== "string") errors.push({ path: `${path}.basic.username_env`, message: "username_env must be a string" })
        if (typeof spec.basic.password_env !== "string") errors.push({ path: `${path}.basic.password_env`, message: "password_env must be a string" })
        break;
      case "bearer":
        if (typeof spec.bearer.token_env !== "string") errors.push({ path: `${path}.bearer.token_env`, message: "token_env must be a string" })
        break;
      case "oauth2":
        if (typeof spec.oauth2.client_id_env !== "string") errors.push({ path: `${path}.oauth2.client_id_env`, message: "client_id_env must be a string" })
        if (typeof spec.oauth2.client_secret_env !== "string") errors.push({ path: `${path}.oauth2.client_secret_env`, message: "client_secret_env must be a string" })
        if (typeof spec.oauth2.token_url !== "string") errors.push({ path: `${path}.oauth2.token_url`, message: "token_url must be a string" })
        break;
      default:
        errors.push({ path, message: `unknown auth type: ${authType}` })
    }
  }
}

function validateOperationSpec (errors: ValidationError[], path: string, opName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "operation spec must be an object" })

  const validMethods = ["GET", "POST", "PUT", "DELETE", "PATCH"];
  if (typeof spec.method !== "string" || !validMethods.includes(spec.method)) {
    errors.push({ path: `${path}.method`, message: `method must be one of: ${validMethods.join(', ')}` })
  }

  if (typeof spec.path !== "string") errors.push({ path: `${path}.path`, message: "path must be a string" })

  if (spec.request_format !== undefined) {
    validateRequestFormat(errors, `${path}.request_format`, spec.request_format)
  }

  if (spec.response_format !== undefined) {
    validateResponseFormat(errors, `${path}.response_format`, spec.response_format)
  }

  if (spec.sync !== undefined && typeof spec.sync !== "boolean") errors.push({ path: `${path}.sync`, message: "sync must be a boolean" })
  if (spec.async_return_address !== undefined && typeof spec.async_return_address !== "boolean") errors.push({ path: `${path}.async_return_address`, message: "async_return_address must be a boolean" })
  if (spec.timeout_ms !== undefined && typeof spec.timeout_ms !== "number") errors.push({ path: `${path}.timeout_ms`, message: "timeout_ms must be a number" })

  if (spec.retry_policy !== undefined) {
    validateRetryPolicy(errors, `${path}.retry_policy`, spec.retry_policy)
  }
}

function validateRequestFormat (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "request format must be an object" })

  const validContentTypes = ["application/json", "application/x-www-form-urlencoded", "multipart/form-data"];
  if (typeof spec.content_type !== "string") errors.push({ path: `${path}.content_type`, message: "content_type must be a string" })
  else if (!validContentTypes.includes(spec.content_type) && !spec.content_type.startsWith("application/") && !spec.content_type.startsWith("text/")) {
    errors.push({ path: `${path}.content_type`, message: `content_type must be a valid content type` })
  }

  if (spec.body_mapping !== undefined) {
    if (!isObject(spec.body_mapping)) errors.push({ path: `${path}.body_mapping`, message: "body_mapping must be an object" })
    else {
      for (const [k, v] of Object.entries(spec.body_mapping)) {
        validateExpr(errors, `${path}.body_mapping.${k}`, v)
      }
    }
  }

  if (spec.query_params !== undefined) {
    if (!isObject(spec.query_params)) errors.push({ path: `${path}.query_params`, message: "query_params must be an object" })
    else {
      for (const [k, v] of Object.entries(spec.query_params)) {
        validateExpr(errors, `${path}.query_params.${k}`, v)
      }
    }
  }

  if (spec.headers !== undefined) {
    if (!isObject(spec.headers)) errors.push({ path: `${path}.headers`, message: "headers must be an object" })
    else {
      for (const [k, v] of Object.entries(spec.headers)) {
        validateExpr(errors, `${path}.headers.${k}`, v)
      }
    }
  }
}

function validateResponseFormat (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "response format must be an object" })

  if (spec.success_codes !== undefined) {
    if (!Array.isArray(spec.success_codes)) errors.push({ path: `${path}.success_codes`, message: "success_codes must be an array" })
    else {
      for (let i = 0; i < spec.success_codes.length; i++) {
        if (typeof spec.success_codes[i] !== "number") errors.push({ path: `${path}.success_codes[${i}]`, message: "each success code must be a number" })
      }
    }
  }

  if (spec.body_mapping !== undefined) {
    if (!isObject(spec.body_mapping)) errors.push({ path: `${path}.body_mapping`, message: "body_mapping must be an object" })
    else {
      for (const [k, v] of Object.entries(spec.body_mapping)) {
        validateExpr(errors, `${path}.body_mapping.${k}`, v)
      }
    }
  }

  if (spec.error_mapping !== undefined) {
    if (!isObject(spec.error_mapping)) errors.push({ path: `${path}.error_mapping`, message: "error_mapping must be an object" })
    else {
      for (const [k, v] of Object.entries(spec.error_mapping)) {
        validateExpr(errors, `${path}.error_mapping.${k}`, v)
      }
    }
  }
}

function validateCircuitBreaker (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "circuit breaker must be an object" })

  if (typeof spec.failure_threshold !== "number") errors.push({ path: `${path}.failure_threshold`, message: "failure_threshold must be a number" })
  if (typeof spec.timeout_ms !== "number") errors.push({ path: `${path}.timeout_ms`, message: "timeout_ms must be a number" })
  if (typeof spec.success_threshold !== "number") errors.push({ path: `${path}.success_threshold`, message: "success_threshold must be a number" })
}

function validateMigration (errors: ValidationError[], path: string, migrationName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "migration spec must be an object" })

  if (typeof spec.from_version !== "number") errors.push({ path: `${path}.from_version`, message: "from_version must be a number" })
  if (typeof spec.to_version !== "number") errors.push({ path: `${path}.to_version`, message: "to_version must be a number" })
  if (typeof spec.on_type !== "string") errors.push({ path: `${path}.on_type`, message: "on_type must be a string" })

  if (!isObject(spec.event_transforms)) errors.push({ path: `${path}.event_transforms`, message: "event_transforms must be an object" })
  else {
    for (const [transformName, transformSpec] of Object.entries(spec.event_transforms)) {
      validateEventTransform(errors, `${path}.event_transforms.${transformName}`, transformName, transformSpec)
    }
  }

  if (spec.state_map !== undefined) {
    if (!isObject(spec.state_map)) errors.push({ path: `${path}.state_map`, message: "state_map must be an object" })
    else {
      for (const [fromState, toState] of Object.entries(spec.state_map)) {
        if (typeof fromState !== "string") errors.push({ path: `${path}.state_map.${fromState}`, message: "state_map keys must be strings" })
        if (typeof toState !== "string") errors.push({ path: `${path}.state_map.${fromState}`, message: "state_map values must be strings" })
      }
    }
  }
}

function validateEventTransform (errors: ValidationError[], path: string, transformName: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "event transform must be an object" })

  if (spec.emit_as !== undefined && typeof spec.emit_as !== "string") errors.push({ path: `${path}.emit_as`, message: "emit_as must be a string" })

  if (spec.payload_map !== undefined) {
    if (!isObject(spec.payload_map)) errors.push({ path: `${path}.payload_map`, message: "payload_map must be an object" })
    else {
      for (const [k, v] of Object.entries(spec.payload_map)) {
        validateExpr(errors, `${path}.payload_map.${k}`, v)
      }
    }
  }

  if (spec.drop !== undefined && typeof spec.drop !== "boolean") errors.push({ path: `${path}.drop`, message: "drop must be a boolean" })

  if (spec.fan_out !== undefined) {
    validateFanOutTransform(errors, `${path}.fan_out`, spec.fan_out)
  }
}

function validateFanOutTransform (errors: ValidationError[], path: string, spec: any) {
  if (!isObject(spec)) return void errors.push({ path, message: "fan_out must be an object" })

  if (!Array.isArray(spec.emit_many)) errors.push({ path: `${path}.emit_many`, message: "emit_many must be an array" })
  else {
    for (let i = 0; i < spec.emit_many.length; i++) {
      const item = spec.emit_many[i];
      const itemPath = `${path}.emit_many[${i}]`;
      
      if (!isObject(item)) {
        errors.push({ path: itemPath, message: "fan_out emit_many items must be objects" })
        continue
      }

      if (typeof item.emit_as !== "string") errors.push({ path: `${itemPath}.emit_as`, message: "emit_many[].emit_as must be a string" })

      if (item.payload_map !== undefined) {
        if (!isObject(item.payload_map)) errors.push({ path: `${itemPath}.payload_map`, message: "payload_map must be an object" })
        else {
          for (const [k, v] of Object.entries(item.payload_map)) {
            validateExpr(errors, `${itemPath}.payload_map.${k}`, v)
          }
        }
      }

      if (item.condition !== undefined) {
        validateExpr(errors, `${itemPath}.condition`, item.condition)
      }
    }
  }
}