# Core IR Grammar and Typing Rules (v0)

## Grammar (EBNF-style)

```
CoreIr      := { version:0, types:TypeMap, ... }
TypeSpec    := { id_type, states, initial_state, attrs, shadows?, commands, reducer }
Command     := { input, guard:{expr:Expr}, emits:[Emit+] }
Emit        := { event_type:String, payload:ExprMap }
ReducerOp   := set_state | set_attr | clear_attr | set_shadow
Expr        := lit | var | get | has | obj | arr | bool_ops | rel_ops | num_ops | if | coalesce | is_null | call
Query       := { source:Source, pipeline:[Op*] }
Constraint  := snapshot | bool_query
View        := { kind, on_type, query, row_policy? }
```

## Typing Judgments

Notation:

- `Gamma` environment for vars
- `Gamma |- e : tau` expression typing

Selected rules:

1. `Gamma |- lit(v) : type(v)`
2. `Gamma |- var(x) : Gamma(x)` if `x in dom(Gamma)`
3. `Gamma |- eq(e1,e2) : bool` if `Gamma |- e1 : tau` and `Gamma |- e2 : tau`
4. `Gamma |- and([e*]) : bool` if each `Gamma |- ei : bool`
5. `Gamma |- call(fn,args) : tau_fn` iff intrinsic signature admits arg types

Reducer typing:

- `set_attr(name, expr)` valid only if `name` declared in attrs and expr type compatible.
- `set_shadow(name, expr)` valid only if `name` declared in shadows and type compatible.
- `set_state(expr)` requires `expr : string` and value in declared state set (runtime/typecheck constrained).

Query typing:

- Pipeline ops preserve a well-formed row relation.
- `group_by` introduces aggregate fields into row scope.
- `order_by` expressions typed in current row scope.
