# /docs/spec/core-ir-ast.md

# Core IR v0 — Typed AST (Normative)

## 0. Status

This document defines the typed Abstract Syntax Tree (AST) for Core IR v0.

This specification is normative.
Implementations MUST represent all Core IR expressions, queries, reducers, constraints, SLAs, and migrations using these node types only.

---

## 1. Expression AST

All expressions MUST be represented using the following node types.

### 1.1 Literals

```json
{ "lit": { "null": true } }
{ "lit": { "bool": true } }
{ "lit": { "int": 123 } }
{ "lit": { "float": 1.23 } }
{ "lit": { "string": "x" } }
```

### 1.2 Variable References

```json
{ "var": { "now": true } }
{ "var": { "actor": true } }
{ "var": { "state": true } }
{ "var": { "input": { "field": "title" } } }
{ "var": { "attrs": { "field": "severity" } } }
{ "var": { "row": { "field": "state" } } }
{ "var": { "arg": { "name": "limit" } } }
```

---

### 1.3 Boolean Operators

```json
{ "not": <Expr> }
{ "and": [ <Expr>, <Expr> ] }
{ "or":  [ <Expr>, <Expr> ] }
{ "bool": <Expr> }
```

---

### 1.4 Comparisons

```json
{ "eq": [ <Expr>, <Expr> ] }
{ "ne": [ <Expr>, <Expr> ] }
{ "lt": [ <Expr>, <Expr> ] }
{ "le": [ <Expr>, <Expr> ] }
{ "gt": [ <Expr>, <Expr> ] }
{ "ge": [ <Expr>, <Expr> ] }
{ "in": { "needle": <Expr>, "haystack": <Expr> } }
```

---

### 1.5 Arithmetic

```json
{ "add": [ <Expr>, <Expr> ] }
{ "sub": [ <Expr>, <Expr> ] }
{ "mul": [ <Expr>, <Expr> ] }
{ "div": [ <Expr>, <Expr> ] }
```

---

### 1.6 Conditionals

```json
{ "if": { "cond": <Expr>, "then": <Expr>, "else": <Expr> } }
{ "coalesce": [ <Expr>, <Expr> ] }
{ "is_null": <Expr> }
```

---

### 1.7 Calls

```json
{ "call": { "fn": "auth_ok", "args": [ <Expr>, <Expr> ] } }
{ "call": { "fn": "constraint", "args": [ <Expr>, <Expr> ] } }
```

---

## 2. Query AST

Queries MUST be represented as pipelines over sources.

```json
{
  "source": { "snap": { "type": "Ticket" } },
  "pipeline": [
    { "filter": <Expr> },
    { "project": { "fields": [ { "name": "entity_id", "expr": <Expr> } ] } },
    { "order_by": [ { "expr": <Expr>, "dir": "asc" } ] },
    { "limit": 10 }
  ]
}
```

---

## 3. Reducer AST

```json
{ "set_state": { "expr": <Expr> } }
{ "set_attr":  { "name": "title", "expr": <Expr> } }
{ "clear_attr":{ "name": "assignee" } }
{ "set_shadow":{ "name": "severity_i", "expr": <Expr> } }
```

---

## 4. Constraint AST

```json
{
  "id": "no_dup_open",
  "kind": "bool_query",
  "args": { "title": { "type": "string" } },
  "query": <Query>,
  "assert": <Expr>
}
```

---

## 5. SLA AST

```json
{
  "name": "first_response",
  "on_type": "Ticket",
  "start": { "event": <EventSelector> },
  "stop":  { "event": <EventSelector> },
  "within_seconds": 14400,
  "enforce": { "notify": { "emit_event": "sla_breached", "payload": { "name": <Expr> } } }
}
```

---

## 6. Migration AST

```json
{
  "from": 0,
  "to": 1,
  "transforms": [
    {
      "event_type": "created",
      "map": <Expr>
    }
  ]
}
```

---

## 7. Closure

No Core IR construct may be represented using strings or code fragments.
Any construct not representable in this AST is not part of CICSC v0.
