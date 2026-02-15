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
