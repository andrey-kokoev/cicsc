# CICSC Surface Language EBNF

This document defines the grammar for the CICSC ergonomic surface language (DSL).

## Grammar (EBNF)

```ebnf
spec = [ "version" <version_number> ] { declaration } ;

declaration = entity_decl
            | view_decl
            | constraint_decl
            | policy_decl
            | sla_decl
            | migration_decl ;

constraint_decl = "constraint" [ <identifier> ] ":"
                    indent
                    { constraint_item }
                    dedent ;

constraint_item = "on" <identifier>
                | "when" <expression>
                | "assert" <expression> ;

entity_decl = "entity" <identifier> ":"
                indent
                { entity_item }
                dedent ;

entity_item = states_clause
            | initial_clause
            | attr_decl
            | shadow_decl
            | command_decl
            | reducer_decl ;

states_clause = "states" ":" "[" <identifier> { "," <identifier> } "]" ;
initial_clause = "initial" ":" <identifier> ;

attr_decl = "attr" <identifier> ":" <type_expr> [ "optional" ] ;
shadow_decl = "shadow" <identifier> ":" <type_expr> ;

command_decl = "command" <identifier> ":"
                indent
                { command_item }
                dedent ;

command_item = input_clause
             | when_clause
             | auth_clause
             | emit_clause ;

input_clause = "input" <identifier> ":" <type_expr> [ "optional" ] ;
when_clause = "when" <expression> ;
auth_clause = "auth" <expression> ;
emit_clause = "emit" <event_expr> { "," <event_expr> } ;

event_expr = <identifier> [ "(" [ arg_assignment { "," arg_assignment } ] ")" ] ;
arg_assignment = <identifier> ":" <expression> ;

view_decl = "view" <identifier> ":"
             indent
             { view_item }
             dedent ;

view_item = "on" <identifier>
          | "where" <expression>
          | "order_by" <identifier> [ "asc" | "desc" ]
          | "limit" <integer> ;

type_expr = "string" | "int" | "float" | "bool" | "time" | enum_expr ;
enum_expr = "enum" "[" <identifier> { "," <identifier> } "]" ;

expression = /* standard logical/relational expressions */ ;
```

## Considerations

- **Indentation:** The language uses Python-like indentation to define blocks.
- **Keywords:** Minimalist keywords (`entity`, `attr`, `command`, `view`, etc.) to keep it readable for non-programmers.
- **Sugar:**
    - Implicit `emit`: If a command `X` has no `emit` clause, it implicitly emits an event `Xed` (or similar) with all inputs as payload.
    - Default Initial: If `initial` is omitted, the first state in `states` is used.
    - Predicate Sugar: `when state is Open` instead of `when state == "Open"`.
    - Attr shorthand: `attr title` (defaults to string).
