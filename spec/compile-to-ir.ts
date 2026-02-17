import type { CoreIrV0 } from "../core/ir/types"
import type { SpecV0 } from "./ast"

export function compileSpecV0ToCoreIr (spec: SpecV0): CoreIrV0 {
  const types: CoreIrV0["types"] = {}
  for (const [name, e] of Object.entries(spec.entities ?? {})) {
    types[name] = {
      id_type: e.id,
      states: e.states,
      initial_state: e.initial,
      attrs: e.attributes ?? {},
      shadows: e.shadows ?? {},
      commands: mapCommands(e.commands ?? {}, name),
      reducer: mapReducers(e.reducers ?? {}),
      row_policy: e.row_policy ? lowerRowPolicy(e.row_policy) : undefined,
    } as any
  }

  const constraints = mapConstraints(spec.constraints ?? {})
  const views = mapViews(spec.views ?? {})
  const slas = mapSlas(spec.slas ?? {})
  const schedules = mapSchedules(spec.schedules ?? {})
  const workflows = mapWorkflows(spec.workflows ?? {})
  const multi_entity_commands = mapMultiEntityCommands(spec.multi_entity_commands ?? {})
  const ui = mapUiSpecs(spec.ui ?? {})
  const services = mapServices(spec.services ?? {})
  const migrations = mapMigrations(spec.migrations ?? {})
  const policies = mapPolicies(spec.policies ?? {})
  const subscriptions = mapSubscriptions(spec.subscriptions ?? {})
  const webhooks = mapWebhooks(spec.webhooks ?? {})
  const rowPolicies = mapRowPolicies(spec.row_policies ?? {})

  return {
    version: 0,
    types,
    policies: Object.keys(policies).length ? policies : undefined,
    constraints: Object.keys(constraints).length ? constraints : undefined,
    views: Object.keys(views).length ? views : undefined,
    slas: Object.keys(slas).length ? slas : undefined,
    schedules: Object.keys(schedules).length ? schedules : undefined,
    workflows: Object.keys(workflows).length ? workflows : undefined,
    multi_entity_commands: Object.keys(multi_entity_commands).length ? multi_entity_commands : undefined,
    ui: Object.keys(ui).length ? ui : undefined,
    services: Object.keys(services).length ? services : undefined,
    migrations: Object.keys(migrations).length ? migrations : undefined,
    subscriptions: Object.keys(subscriptions).length ? subscriptions : undefined,
    webhooks: Object.keys(webhooks).length ? webhooks : undefined,
    row_policies: Object.keys(rowPolicies).length ? rowPolicies : undefined,
  }
}

function mapCommands (commands: Record<string, any>, entityName: string) {
  const out: Record<string, any> = {}
  for (const [name, c] of Object.entries(commands)) {
    const baseGuard = lowerGuard((c as any).when)
    const authGuard = lowerAuthGuard((c as any).auth, entityName, name)
    const guardExpr = authGuard ? { and: [baseGuard, authGuard] } : baseGuard

    out[name] = {
      input: c.inputs ?? {},
      guard: { expr: guardExpr },
      emits: (c.emit ?? []).map((x: any) => ({
        event_type: String(x.type),
        payload: x.payload ?? {},
      })),
    }
  }
  return out
}

function lowerAuthGuard (auth: any, entityName: string, commandName: string): any | null {
  if (!auth || typeof auth !== "object" || Array.isArray(auth)) return null
  const cmdref = String(auth.cmdref ?? auth.policy ?? `${entityName}.${commandName}`)
  return {
    call: {
      fn: "auth_ok",
      args: [{ var: { actor: true } }, { lit: { string: cmdref } }],
    },
  }
}

function lowerGuard (when: any): any {
  if (when == null) return { lit: { bool: true } }
  if (isExprTaggedObject(when)) return when
  if (!when || typeof when !== "object" || Array.isArray(when)) {
    throw new Error("guard sugar must be an object")
  }

  if (Array.isArray((when as any).all)) {
    return { and: (when as any).all.map((x: any) => lowerGuard(x)) }
  }
  if (Array.isArray((when as any).any)) {
    return { or: (when as any).any.map((x: any) => lowerGuard(x)) }
  }

  const parts: any[] = []
  if (typeof (when as any).state_is === "string") {
    parts.push({
      eq: [
        { var: { state: true } },
        { lit: { string: String((when as any).state_is) } },
      ],
    })
  }
  if (typeof (when as any).role_is === "string") {
    parts.push({
      call: {
        fn: "has_role",
        args: [{ var: { actor: true } }, { lit: { string: String((when as any).role_is) } }],
      },
    })
  }

  if (!parts.length) throw new Error("unsupported guard sugar shape")
  if (parts.length === 1) return parts[0]
  return { and: parts }
}

function mapConstraints (constraints: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, c] of Object.entries(constraints)) {
    if (c.kind === "snapshot") {
      out[name] = { kind: "snapshot", on_type: c.entity, expr: c.when }
    } else if (c.kind === "bool_query") {
      out[name] = {
        kind: "bool_query",
        on_type: c.entity,
        args: c.args ?? {},
        query: c.query,
        assert: c.assert,
      }
    } else {
      throw new Error(`unknown constraint kind: ${String((c as any)?.kind ?? "?")}`)
    }
  }
  return out
}

function mapViews (views: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, v] of Object.entries(views)) {
    const query = v.query ?? lowerViewSugar(v)
    out[name] = {
      kind: v.kind ?? "metric",
      on_type: v.on,
      query,
      row_policy: v.row_policy ? lowerRowPolicy(v.row_policy) : undefined,
    }
  }
  return out
}

function mapMigrations (migrations: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, m] of Object.entries(migrations ?? {})) {
    const from = Number((m as any).from)
    const to = Number((m as any).to)
    if (!Number.isInteger(from) || !Number.isInteger(to) || to !== from + 1) {
      throw new Error(`migration '${name}' must define adjacent versions (from N to N+1)`)
    }

    out[name] = {
      from_version: from,
      to_version: to,
      on_type: String((m as any).entity ?? ""),
      event_transforms: mapEventTransforms((m as any).event_transforms ?? {}),
      state_map: (m as any).state_map ?? undefined,
    }
  }
  return out
}

function mapPolicies (policies: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, p] of Object.entries(policies ?? {})) {
    out[name] = {
      params: Array.isArray((p as any).params) ? (p as any).params.map(String) : [],
      expr: lowerGuard((p as any).allow ?? null),
    }
  }
  return out
}

function mapSlas (slas: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, s] of Object.entries(slas ?? {})) {
    // Determine enforcement type based on spec properties
    let enforce: any = { none: true }; // default
    
    if ((s as any).enforce_notify) {
      enforce = {
        notify: {
          emit_event: String((s as any).enforce_notify?.emit_event ?? ""),
          payload: mapExprRecord((s as any).enforce_notify?.payload ?? {}),
        }
      };
    } else if ((s as any).enforce_auto_transition) {
      enforce = {
        auto_transition: {
          to_state: String((s as any).enforce_auto_transition?.to_state ?? "")
        }
      };
    } else if ((s as any).enforce === "none") {
      enforce = { none: true };
    }
    
    out[name] = {
      name,
      on_type: String((s as any).on ?? ""),
      start: { event: { 
        name: String((s as any).start_event ?? ""), 
        occurrence: (s as any).start_occurrence ? String((s as any).start_occurrence) : undefined,
        where: (s as any).start_where ? lowerGuard((s as any).start_where) : undefined
      }},
      stop: { event: { 
        name: String((s as any).stop_event ?? ""),
        occurrence: (s as any).stop_occurrence ? String((s as any).stop_occurrence) : undefined,
        where: (s as any).stop_where ? lowerGuard((s as any).stop_where) : undefined
      }},
      within_seconds: Number((s as any).within_seconds ?? 0),
      enforce,
    }
  }
  return out
}

function mapSchedules (schedules: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, s] of Object.entries(schedules ?? {})) {
    // Map the trigger
    let trigger: any = {};
    if ((s as any).trigger_cron) {
      trigger = { cron: { expression: String((s as any).trigger_cron.expression || ""), timezone: (s as any).trigger_cron.timezone } }
    } else if ((s as any).trigger_delay) {
      trigger = { delay: { seconds: Number((s as any).trigger_delay.seconds || 0) } }
    } else if ((s as any).trigger_event) {
      trigger = { 
        event: { 
          on_type: String((s as any).trigger_event.on_type || ""),
          event_type: String((s as any).trigger_event.event_type || ""),
          where: (s as any).trigger_event.where ? lowerGuard((s as any).trigger_event.where) : undefined
        }
      }
    }

    // Map the action target
    let target: any = {};
    if ((s as any).action_target_command) {
      target = { 
        command: { 
          entity_type: String((s as any).action_target_command.entity_type || ""),
          entity_id_expr: (s as any).action_target_command.entity_id_expr ? lowerGuard((s as any).action_target_command.entity_id_expr) : undefined,
          command_name: String((s as any).action_target_command.command_name || "")
        }
      }
    } else if ((s as any).action_target_webhook) {
      target = { 
        webhook: { 
          url: String((s as any).action_target_webhook.url || ""),
          method: (s as any).action_target_webhook.method ? String((s as any).action_target_webhook.method) : undefined
        }
      }
    } else if ((s as any).action_target_queue) {
      target = { 
        queue: { 
          name: String((s as any).action_target_queue.name || "")
        }
      }
    }

    // Map the action
    const action = {
      target,
      input_map: (s as any).action_input_map ? mapExprRecord((s as any).action_input_map) : undefined,
      retry_policy: (s as any).action_retry_policy ? mapRetryPolicy((s as any).action_retry_policy) : undefined
    }

    out[name] = {
      name,
      trigger,
      action,
      enabled: (s as any).enabled !== undefined ? Boolean((s as any).enabled) : undefined,
      metadata: (s as any).metadata || undefined
    }
  }
  return out
}

function mapWorkflows (workflows: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, w] of Object.entries(workflows ?? {})) {
    // Map the steps
    const steps: Record<string, any> = {}
    for (const [stepName, stepSpec] of Object.entries((w as any).steps || {})) {
      steps[stepName] = mapWorkflowStep(stepSpec)
    }

    out[name] = {
      name,
      steps,
      start_step: String((w as any).start_step || ""),
      compensation: (w as any).compensation ? mapWorkflowCompensation((w as any).compensation) : undefined,
      metadata: (w as any).metadata || undefined
    }
  }
  return out
}

function mapWorkflowStep (step: any) {
  if ((step as any).command) {
    const cmdSpec = (step as any).command
    let target: any = {}
    
    if (cmdSpec.target_command) {
      target = { 
        command: { 
          entity_type: String(cmdSpec.target_command.entity_type || ""),
          entity_id_expr: cmdSpec.target_command.entity_id_expr ? lowerGuard(cmdSpec.target_command.entity_id_expr) : undefined,
          command_name: String(cmdSpec.target_command.command_name || "")
        }
      }
    } else if (cmdSpec.target_webhook) {
      target = { 
        webhook: { 
          url: String(cmdSpec.target_webhook.url || ""),
          method: cmdSpec.target_webhook.method ? String(cmdSpec.target_webhook.method) : undefined
        }
      }
    } else if (cmdSpec.target_queue) {
      target = { 
        queue: { 
          name: String(cmdSpec.target_queue.name || "")
        }
      }
    }

    return {
      command: {
        target,
        input_map: cmdSpec.input_map ? mapExprRecord(cmdSpec.input_map) : undefined,
        on_success: cmdSpec.on_success ? String(cmdSpec.on_success) : undefined,
        on_failure: cmdSpec.on_failure ? String(cmdSpec.on_failure) : undefined,
        retry_policy: cmdSpec.retry_policy ? mapRetryPolicy(cmdSpec.retry_policy) : undefined
      }
    }
  } else if ((step as any).wait) {
    const waitSpec = (step as any).wait
    return {
      wait: {
        timeout_seconds: waitSpec.timeout_seconds !== undefined ? Number(waitSpec.timeout_seconds) : undefined,
        wait_for_event: waitSpec.wait_for_event ? {
          on_type: String(waitSpec.wait_for_event.on_type || ""),
          event_type: String(waitSpec.wait_for_event.event_type || ""),
          where: waitSpec.wait_for_event.where ? lowerGuard(waitSpec.wait_for_event.where) : undefined
        } : undefined,
        on_timeout: waitSpec.on_timeout ? String(waitSpec.on_timeout) : undefined,
        on_event: waitSpec.on_event ? String(waitSpec.on_event) : undefined
      }
    }
  } else if ((step as any).decision) {
    const decSpec = (step as any).decision
    return {
      decision: {
        condition: decSpec.condition ? lowerGuard(decSpec.condition) : undefined,
        on_true: String(decSpec.on_true || ""),
        on_false: String(decSpec.on_false || "")
      }
    }
  } else if ((step as any).parallel) {
    const parSpec = (step as any).parallel
    const branches: Record<string, any> = {}
    for (const [branchName, branchSpec] of Object.entries(parSpec.branches || {})) {
      branches[branchName] = mapWorkflowStep(branchSpec)
    }
    
    return {
      parallel: {
        branches,
        on_completion: String(parSpec.on_completion || ""),
        on_failure: parSpec.on_failure ? String(parSpec.on_failure) : undefined
      }
    }
  }
  return {}
}

function mapWorkflowCompensation (comp: any) {
  return {
    strategy: String(comp.strategy || "saga"),
    custom_steps: comp.custom_steps ? (() => {
      const steps: Record<string, any> = {}
      for (const [stepName, stepSpec] of Object.entries(comp.custom_steps)) {
        steps[stepName] = mapWorkflowStep(stepSpec)
      }
      return steps
    })() : undefined
  }
}

function mapRetryPolicy (policy: any) {
  return {
    max_attempts: Number(policy.max_attempts || 3),
    backoff: {
      initial_delay_ms: Number(policy.backoff?.initial_delay_ms || 1000),
      max_delay_ms: Number(policy.backoff?.max_delay_ms || 60000),
      multiplier: Number(policy.backoff?.multiplier || 2)
    }
  }
}

function mapEventTransforms (eventTransforms: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [eventType, t] of Object.entries(eventTransforms ?? {})) {
    const transform: any = {
      emit_as: typeof (t as any)?.emit_as === "string" ? (t as any).emit_as : undefined,
      payload_map: (t as any)?.payload_map ? mapExprRecord((t as any).payload_map) : undefined,
      drop: Boolean((t as any)?.drop ?? false),
      fan_out: (t as any)?.fan_out ? mapFanOutTransform((t as any).fan_out) : undefined,
    }
    
    // BQ1.1: Handle emit_many for fan-out
    if (Array.isArray((t as any).emit_many)) {
      transform.emit_many = (t as any).emit_many.map((e: any) => ({
        event_type: String(e.event_type ?? e.type),
        payload: e.payload ?? e.payload_map ?? {},
      }))
    }
    
    out[eventType] = transform
  }
  return out
}

function mapFanOutTransform (fanOut: any) {
  if (!fanOut?.emit_many || !Array.isArray(fanOut.emit_many)) {
    return undefined;
  }
  
  const emitMany = fanOut.emit_many.map((item: any) => ({
    emit_as: String(item.emit_as || ""),
    payload_map: item.payload_map ? mapExprRecord(item.payload_map) : undefined,
    condition: item.condition ? lowerGuard(item.condition) : undefined,
  }));
  
  return {
    emit_many: emitMany
  };
}

function mapReducers (reducers: Record<string, any[]>): Record<string, any[]> {
  const out: Record<string, any[]> = {}
  for (const [eventType, ops] of Object.entries(reducers ?? {})) {
    out[eventType] = (ops ?? []).map((op) => lowerReducerOp(op))
  }
  return out
}

function lowerReducerOp (op: any): any {
  if (!op || typeof op !== "object" || Array.isArray(op)) throw new Error("reducer op must be an object")
  const tag = Object.keys(op)[0]
  const body = (op as any)[tag]

  if (tag === "set_state") {
    if (body && typeof body === "object" && "expr" in body) return op
    return { set_state: { expr: wrapExpr(body) } }
  }

  if (tag === "set_attr") {
    if (body && typeof body === "object" && "name" in body && "expr" in body) return op
    if (body && typeof body === "object" && typeof body.field === "string" && "value" in body) {
      return { set_attr: { name: body.field, expr: wrapExpr(body.value) } }
    }
    throw new Error("set_attr sugar expects { field, value }")
  }

  if (tag === "set_shadow") {
    if (body && typeof body === "object" && "name" in body && "expr" in body) return op
    if (body && typeof body === "object" && typeof body.field === "string" && "value" in body) {
      return { set_shadow: { name: body.field, expr: wrapExpr(body.value) } }
    }
    throw new Error("set_shadow sugar expects { field, value }")
  }

  if (tag === "clear_attr") {
    if (body && typeof body === "object" && typeof body.name === "string") return op
    if (typeof body === "string") return { clear_attr: { name: body } }
    throw new Error("clear_attr sugar expects string attr name")
  }

  return op
}

const EXPR_TAGS = new Set([
  "lit", "var", "get", "has", "obj", "arr",
  "not", "and", "or", "bool",
  "eq", "ne", "lt", "le", "gt", "ge", "in",
  "add", "sub", "mul", "div",
  "if", "coalesce", "is_null",
  "time_between", "map_enum",
  "call",
])

function isExprTaggedObject (v: any): boolean {
  if (!v || typeof v !== "object" || Array.isArray(v)) return false
  const ks = Object.keys(v)
  return ks.length === 1 && EXPR_TAGS.has(ks[0]!)
}

function wrapExpr (v: any): any {
  if (isExprTaggedObject(v)) return v
  if (v === null) return { lit: { null: true } }
  if (typeof v === "boolean") return { lit: { bool: v } }
  if (typeof v === "number") return Number.isInteger(v) ? { lit: { int: v } } : { lit: { float: v } }
  if (typeof v === "string") return { lit: { string: v } }
  throw new Error("unsupported reducer sugar literal")
}

function lowerViewSugar (v: any): any {
  if (!v || typeof v !== "object") throw new Error("view must be object")
  if (!v.lanes || typeof v.lanes !== "object") throw new Error("view.query missing and no lanes sugar provided")

  const lanes = v.lanes as any
  const pipeline: any[] = []

  if (Array.isArray(lanes.states) && lanes.states.length > 0) {
    pipeline.push({
      filter: {
        in: {
          needle: { var: { row: { field: "state" } } },
          haystack: { arr: { items: lanes.states.map((s: string) => ({ lit: { string: String(s) } })) } },
        },
      },
    })
  }

  if (lanes.order_by && typeof lanes.order_by === "object" && typeof lanes.order_by.field === "string") {
    pipeline.push({
      order_by: [
        {
          expr: { var: { row: { field: lanes.order_by.field } } },
          dir: lanes.order_by.dir === "asc" ? "asc" : "desc",
        },
      ],
    })
  }

  if (typeof lanes.limit === "number") {
    pipeline.push({ limit: Math.max(0, Math.trunc(lanes.limit)) })
  }

  return {
    source: { snap: { type: String(v.on) } },
    pipeline,
  }
}

function mapSubscriptions (subscriptions: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, s] of Object.entries(subscriptions)) {
    out[name] = {
      on_type: String(s.on),
      filter: s.filter ? lowerSubscriptionFilter(s.filter) : undefined
    }
  }
  return out
}

function lowerSubscriptionFilter (filter: any): any {
  if (filter == null) return filter
  if (typeof filter !== "object") return filter

  if (filter.var && filter.var.input) {
    return { var: { row: { field: filter.var.input.field } } }
  }

  if (Array.isArray(filter)) {
    return filter.map(x => lowerSubscriptionFilter(x))
  }

  const out: any = {}
  for (const [k, v] of Object.entries(filter)) {
    out[k] = lowerSubscriptionFilter(v)
  }
  return out
}

function mapMultiEntityCommands (commands: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, c] of Object.entries(commands ?? {})) {
    out[name] = {
      name,
      steps: (c as any).steps ? (c as any).steps.map(mapMultiEntityCommandStep) : [],
      transaction_boundary: {
        kind: String((c as any).transaction_boundary?.kind || "atomic"),
        isolation_level: (c as any).transaction_boundary?.isolation_level ? String((c as any).transaction_boundary.isolation_level) : undefined
      },
      compensation_strategy: (c as any).compensation_strategy ? {
        strategy: String((c as any).compensation_strategy.strategy || "saga"),
        saga_steps: (c as any).compensation_strategy.saga_steps ? (c as any).compensation_strategy.saga_steps.map(mapCompensationStep) : undefined
      } : undefined,
      partial_failure_handling: {
        strategy: String((c as any).partial_failure_handling?.strategy || "fail_fast"),
        on_failure: (c as any).partial_failure_handling?.on_failure ? String((c as any).partial_failure_handling.on_failure) : undefined
      }
    }
  }
  return out
}

function mapMultiEntityCommandStep (step: any) {
  if (step.command) {
    return {
      command: {
        entity_type: String(step.command.entity_type || ""),
        entity_id_expr: step.command.entity_id_expr ? lowerGuard(step.command.entity_id_expr) : undefined,
        command_name: String(step.command.command_name || ""),
        input: step.command.input ? mapExprRecord(step.command.input) : {}
      }
    }
  } else if (step.wait) {
    return {
      wait: {
        duration_ms: Number(step.wait.duration_ms || 0)
      }
    }
  } else if (step.condition) {
    return {
      condition: {
        expr: step.condition.expr ? lowerGuard(step.condition.expr) : undefined,
        then_steps: step.condition.then_steps ? step.condition.then_steps.map(mapMultiEntityCommandStep) : [],
        else_steps: step.condition.else_steps ? step.condition.else_steps.map(mapMultiEntityCommandStep) : []
      }
    }
  }
  return {}
}

function mapCompensationStep (step: any) {
  return {
    entity_type: String(step.entity_type || ""),
    entity_id_expr: step.entity_id_expr ? lowerGuard(step.entity_id_expr) : undefined,
    command_name: String(step.command_name || ""),
    input: step.input ? mapExprRecord(step.input) : {}
  }
}

function mapUiSpecs (uiSpecs: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, uiSpec] of Object.entries(uiSpecs ?? {})) {
    out[name] = {
      screens: uiSpec.screens ? mapScreens(uiSpec.screens) : undefined,
      dashboards: uiSpec.dashboards ? mapDashboards(uiSpec.dashboards) : undefined,
      navigation: uiSpec.navigation ? mapNavigation(uiSpec.navigation) : undefined,
      themes: uiSpec.themes ? mapThemes(uiSpec.themes) : undefined,
    }
  }
  return out
}

function mapServices (services: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, s] of Object.entries(services ?? {})) {
    out[name] = {
      name,
      base_url: String((s as any).base_url || ""),
      auth: (s as any).auth ? mapServiceAuth((s as any).auth) : undefined,
      operations: (s as any).operations ? mapOperations((s as any).operations) : {},
      retry_policy: (s as any).retry_policy ? mapRetryPolicy((s as any).retry_policy) : undefined,
      circuit_breaker: (s as any).circuit_breaker ? mapCircuitBreaker((s as any).circuit_breaker) : undefined,
      timeout_ms: (s as any).timeout_ms !== undefined ? Number((s as any).timeout_ms) : undefined,
    }
  }
  return out
}

function mapServiceAuth (auth: any) {
  if (!auth) return undefined
  
  const authKeys = Object.keys(auth)
  if (authKeys.length !== 1) return undefined
  
  const authType = authKeys[0]
  const authSpec = auth[authType]
  
  switch (authType) {
    case "api_key":
      return {
        api_key: {
          header: String(authSpec.header || "Authorization"),
          env_var: String(authSpec.env_var || ""),
        }
      }
    case "basic":
      return {
        basic: {
          username_env: String(authSpec.username_env || ""),
          password_env: String(authSpec.password_env || ""),
        }
      }
    case "bearer":
      return {
        bearer: {
          token_env: String(authSpec.token_env || ""),
        }
      }
    case "oauth2":
      return {
        oauth2: {
          client_id_env: String(authSpec.client_id_env || ""),
          client_secret_env: String(authSpec.client_secret_env || ""),
          token_url: String(authSpec.token_url || ""),
        }
      }
    default:
      return undefined
  }
}

function mapOperations (operations: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, op] of Object.entries(operations)) {
    out[name] = {
      method: String(op.method || "GET"),
      path: String(op.path || ""),
      request_format: op.request_format ? mapRequestFormat(op.request_format) : undefined,
      response_format: op.response_format ? mapResponseFormat(op.response_format) : undefined,
      sync: op.sync !== undefined ? Boolean(op.sync) : undefined,
      async_return_address: op.async_return_address !== undefined ? Boolean(op.async_return_address) : undefined,
      timeout_ms: op.timeout_ms !== undefined ? Number(op.timeout_ms) : undefined,
      retry_policy: op.retry_policy ? mapRetryPolicy(op.retry_policy) : undefined,
    }
  }
  return out
}

function mapRequestFormat (format: any) {
  if (!format) return undefined
  return {
    content_type: String(format.content_type || "application/json"),
    body_mapping: format.body_mapping ? mapExprRecord(format.body_mapping) : undefined,
    query_params: format.query_params ? mapExprRecord(format.query_params) : undefined,
    headers: format.headers ? mapExprRecord(format.headers) : undefined,
  }
}

function mapResponseFormat (format: any) {
  if (!format) return undefined
  return {
    success_codes: Array.isArray(format.success_codes) ? format.success_codes.map(Number) : undefined,
    body_mapping: format.body_mapping ? mapExprRecord(format.body_mapping) : undefined,
    error_mapping: format.error_mapping ? mapExprRecord(format.error_mapping) : undefined,
  }
}

function mapCircuitBreaker (breaker: any) {
  if (!breaker) return undefined
  return {
    failure_threshold: Number(breaker.failure_threshold || 5),
    timeout_ms: Number(breaker.timeout_ms || 60000),
    success_threshold: Number(breaker.success_threshold || 3),
  }
}

function mapScreens (screens: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, screen] of Object.entries(screens)) {
    out[name] = {
      title: String(screen.title || ""),
      description: screen.description ? String(screen.description) : undefined,
      layout: mapLayout(screen.layout),
      data_source: mapDataSource(screen.data_source),
      permissions: screen.permissions ? mapPermissions(screen.permissions) : undefined,
    }
  }
  return out
}

function mapDashboards (dashboards: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, dashboard] of Object.entries(dashboards)) {
    out[name] = {
      title: String(dashboard.title || ""),
      description: dashboard.description ? String(dashboard.description) : undefined,
      widgets: Array.isArray(dashboard.widgets) ? dashboard.widgets.map(mapWidget) : [],
      layout: mapLayout(dashboard.layout),
      permissions: dashboard.permissions ? mapPermissions(dashboard.permissions) : undefined,
    }
  }
  return out
}

function mapNavigation (nav: any) {
  if (!nav) return undefined
  return {
    sections: Array.isArray(nav.sections) ? nav.sections.map(mapNavigationSection) : [],
  }
}

function mapNavigationSection (section: any) {
  return {
    id: String(section.id || ""),
    title: String(section.title || ""),
    icon: section.icon ? String(section.icon) : undefined,
    items: Array.isArray(section.items) ? section.items.map(mapNavigationItem) : [],
    permissions: section.permissions ? mapPermissions(section.permissions) : undefined,
  }
}

function mapNavigationItem (item: any) {
  return {
    id: String(item.id || ""),
    title: String(item.title || ""),
    route: String(item.route || ""),
    icon: item.icon ? String(item.icon) : undefined,
    permissions: item.permissions ? mapPermissions(item.permissions) : undefined,
  }
}

function mapLayout (layout: any) {
  if (!layout) return undefined
  
  const layoutKeys = Object.keys(layout);
  if (layoutKeys.length !== 1) return {};
  
  const kind = layoutKeys[0];
  const layoutSpec = layout[kind];
  
  switch (kind) {
    case "grid":
      return {
        grid: {
          columns: Number(layoutSpec.columns || 1),
          items: Array.isArray(layoutSpec.items) ? layoutSpec.items.map(mapLayoutItem) : [],
        }
      };
    case "form":
      return {
        form: {
          fields: Array.isArray(layoutSpec.fields) ? layoutSpec.fields.map(mapFormField) : [],
        }
      };
    case "table":
      return {
        table: {
          columns: Array.isArray(layoutSpec.columns) ? layoutSpec.columns.map(mapTableColumn) : [],
        }
      };
    case "tabs":
      return {
        tabs: {
          tabs: Array.isArray(layoutSpec.tabs) ? layoutSpec.tabs.map(mapTabSpec) : [],
        }
      };
    case "sidebar":
      return {
        sidebar: {
          main: mapLayout(layoutSpec.main),
          sidebar: mapLayout(layoutSpec.sidebar),
        }
      };
    default:
      return {};
  }
}

function mapLayoutItem (item: any) {
  return {
    component: String(item.component || ""),
    props: item.props ? mapExprRecord(item.props) : {},
    col_span: item.col_span !== undefined ? Number(item.col_span) : undefined,
    row_span: item.row_span !== undefined ? Number(item.row_span) : undefined,
  }
}

function mapFormField (field: any) {
  return {
    name: String(field.name || ""),
    label: String(field.label || ""),
    type: String(field.type || "text"),
    required: field.required !== undefined ? Boolean(field.required) : undefined,
    validation: field.validation ? lowerGuard(field.validation) : undefined,
    default_value: field.default_value ? lowerGuard(field.default_value) : undefined,
  }
}

function mapTableColumn (column: any) {
  return {
    name: String(column.name || ""),
    label: String(column.label || ""),
    type: String(column.type || "text"),
    sortable: column.sortable !== undefined ? Boolean(column.sortable) : undefined,
    filterable: column.filterable !== undefined ? Boolean(column.filterable) : undefined,
    formatter: column.formatter ? lowerGuard(column.formatter) : undefined,
  }
}

function mapTabSpec (tab: any) {
  return {
    id: String(tab.id || ""),
    title: String(tab.title || ""),
    content: mapLayout(tab.content),
  }
}

function mapWidget (widget: any) {
  return {
    id: String(widget.id || ""),
    title: String(widget.title || ""),
    type: String(widget.type || "metric"),
    data_source: mapDataSource(widget.data_source),
    config: widget.config ? mapExprRecord(widget.config) : {},
  }
}

function mapDataSource (dataSource: any) {
  if (!dataSource) return undefined
  
  const dsKeys = Object.keys(dataSource);
  if (dsKeys.length !== 1) return {};
  
  const kind = dsKeys[0];
  const dsSpec = dataSource[kind];
  
  switch (kind) {
    case "view":
      return {
        view: {
          view_name: String(dsSpec.view_name || ""),
          args: dsSpec.args ? mapExprRecord(dsSpec.args) : undefined,
        }
      };
    case "entity":
      return {
        entity: {
          entity_type: String(dsSpec.entity_type || ""),
          query: dsSpec.query ? lowerGuard(dsSpec.query) : undefined,
        }
      };
    case "api":
      return {
        api: {
          endpoint: String(dsSpec.endpoint || ""),
          method: dsSpec.method ? String(dsSpec.method) : undefined,
          params: dsSpec.params ? mapExprRecord(dsSpec.params) : undefined,
        }
      };
    default:
      return {};
  }
}

function mapPermissions (perms: any) {
  if (!perms) return undefined
  return {
    roles: Array.isArray(perms.roles) ? perms.roles.map(String) : undefined,
    conditions: Array.isArray(perms.conditions) ? perms.conditions.map(lowerGuard) : undefined,
  }
}

function mapThemes (themes: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, theme] of Object.entries(themes)) {
    out[name] = {
      name: String(theme.name || ""),
      mode: String(theme.mode || "light"),
      colors: theme.colors ? { ...theme.colors } : undefined,
      spacing: theme.spacing ? { ...theme.spacing } : undefined,
      typography: theme.typography ? mapTypography(theme.typography) : undefined,
    }
  }
  return out
}

function mapTypography (typography: any) {
  if (!typography) return undefined
  return {
    font_family: typography.font_family ? String(typography.font_family) : undefined,
    sizes: typography.sizes ? { ...typography.sizes } : undefined,
    weights: typography.weights ? { ...typography.weights } : undefined,
  }
}

function mapWebhooks (webhooks: Record<string, any>) {
  const out: Record<string, any> = {}
  for (const [name, w] of Object.entries(webhooks)) {
    out[name] = {
      on_type: String(w.on),
      command: String(w.command),
      verify: w.verify
    }
  }
  return out
}

// Row-Level Security policy map (BT2.1-BT2.3)
function mapRowPolicies (rowPolicies: Record<string, any>): Record<string, any> {
  const out: Record<string, any> = {}
  for (const [name, policy] of Object.entries(rowPolicies)) {
    out[name] = lowerRowPolicy(policy)
  }
  return out
}

// Row-Level Security policy lowering (BT2.1-BT2.3)
function lowerRowPolicy (policy: any): any {
  if (typeof policy === "string") {
    // Named policy reference - will be resolved at validation time
    return { ref: policy }
  }

  if (!policy || typeof policy !== "object") {
    throw new Error("row_policy must be an object or string reference")
  }

  const keys = Object.keys(policy)
  if (keys.length !== 1) {
    throw new Error("row_policy must have exactly one key (owner, member_of, or expr)")
  }

  const tag = keys[0]!
  const body = policy[tag]

  switch (tag) {
    case "owner":
      return {
        owner: {
          actor_field: String(body.field)
        }
      }
    case "member_of":
      return {
        member_of: {
          actor_field: String(body.field),
          target_type: String(body.through),
          target_field: body.target_field ? String(body.target_field) : "entity_id"
        }
      }
    case "expr":
      return { expr: body }
    default:
      throw new Error(`unknown row_policy tag: ${tag}`)
  }
}
