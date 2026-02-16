# Phase BV: UI Primitive - User Interface Generation

**Status**: PLANNED  
**Agent**: AGENT_GEMINI  
**Goal**: Add `ui` as top-level Core IR primitive for complete user interface generation

## Problem Statement

Current CICSC defines backend (entities, commands, views) but Sarah interacts with:
- **Navigation menus** - Not defined
- **Screen layouts** - Not defined  
- **Forms/tables** - Generated ad-hoc
- **Dashboards** - Not defined

Gap: No first-class UI primitive in Spec.

## Core IR Extension

```typescript
export type CoreIrV0 = {
  // ... existing
  ui?: Record<string, UiSpecV0>  // NEW top-level
}

export type UiSpecV0 = {
  type: "screen" | "dashboard" | "modal"
  
  navigation?: {
    section: string        // "Tickets", "Reports"
    icon?: string          // Iconify icon name
    order?: number
    parent?: string        // For nested menus
    required_role?: string // RBAC filter
  }
  
  layout: {
    header?: string | ExprV0
    sections: UiSectionV0[]
    actions?: UiActionV0[]
  }
  
  data?: {
    source: string         // view name or entity type
    filters?: ExprV0
  }
}

export type UiSectionV0 = 
  | { type: "table"; columns: string[]; row_actions?: string[] }
  | { type: "form"; fields: UiFieldV0[] }
  | { type: "kanban"; lane_field: string }
  | { type: "metrics"; items: UiMetricV0[] }
  | { type: "chart"; chart_type: "line" | "bar"; x_axis: string; y_axis: string }

export type UiFieldV0 = {
  name: string
  type: "text" | "number" | "select" | "date" | "reference" | "textarea"
  component?: string  // Override with custom component
  required?: boolean
  validation?: ValidationRuleV0[]
}
```

## Spec DSL Example

```python
ui TicketList {
  type: screen
  navigation: {
    section: "Tickets"
    icon: "heroicons:ticket"
    order: 1
  }
  
  layout: {
    header: "My Open Tickets"
    
    sections: [
      {
        type: table
        source: view MyOpenTickets
        columns: [id, title, status, priority, created_at]
        row_actions: [command ViewTicket, command EditTicket]
      }
    ]
    
    actions: [
      { command: CreateTicket, primary: true, label: "New Ticket" }
    ]
  }
}

ui TicketForm {
  type: screen
  
  layout: {
    header: "Ticket Details"
    
    sections: [
      {
        type: form
        source: entity Ticket
        
        fields: [
          { name: title, type: text, required: true }
          { name: description, type: textarea }
          { 
            name: status
            type: select
            options: state_transitions
          }
          { 
            name: assignee
            type: reference
            to: entity User
            filter: "user.role == 'agent'"
          }
        ]
      }
    ]
    
    actions: [
      { command: UpdateTicket, primary: true }
      { command: AddComment }
      { command: Escalate, danger: true }
    ]
  }
}

ui TicketDashboard {
  type: dashboard
  navigation: { section: "Reports", icon: "heroicons:chart", order: 2 }
  
  layout: {
    header: "Ticket Metrics"
    
    sections: [
      {
        type: metrics
        items: [
          { label: "Open", value: count(Ticket where status == "open") }
          { label: "Resolved Today", value: count(Ticket where resolved_at == today) }
        ]
      }
      {
        type: chart
        chart_type: line
        title: "Tickets Over Time"
        x_axis: created_at
        y_axis: count()
      }
      {
        type: kanban
        title: "My Tickets"
        source: view MyTicketsByStatus
        lane_field: status
      }
    ]
  }
}
```

## Component Contract (JSON Schema)

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://cicsc.dev/ui-contract/v1",
  
  "DataTable": {
    "props": {
      "columns": { "type": "array" },
      "data": { "type": "array" },
      "pagination": { "type": "object" }
    },
    "capabilities": {
      "sort": { "modes": ["client", "server"], "multiColumn": true },
      "filter": { "types": ["text", "select", "date-range"] },
      "paginate": { "modes": ["offset", "cursor"] },
      "select": { "modes": ["single", "multi"] },
      "virtualize": { "threshold": 1000 }
    }
  },
  
  "FormField": {
    "props": {
      "name": { "type": "string" },
      "type": { "enum": ["text", "number", "select", "date", "reference"] },
      "validation": { "type": "array" }
    },
    "capabilities": {
      "validate": { "timing": ["onChange", "onBlur", "onSubmit"] }
    }
  },
  
  "Button": {
    "props": {
      "label": { "type": "string" },
      "variant": { "enum": ["primary", "secondary", "danger", "ghost"] },
      "loading": { "type": "boolean" }
    }
  }
}
```

## Component Registry

```json
{
  "extends": "@cicsc/shadcn-vue",
  
  "components": {
    "DataTable": {
      "source": "@cicsc/shadcn-vue/table",
      "capabilities": ["sort", "filter", "paginate", "select"]
    },
    "FormField": {
      "source": "@cicsc/shadcn-vue/form"
    },
    "Button": {
      "source": "@cicsc/shadcn-vue/button"
    },
    "NavigationMenu": {
      "source": "@cicsc/shadcn-vue/navigation-menu"
    }
  }
}
```

## Generated Output Structure

```
app/
├── components/
│   └── ui/              # shadcn components (from registry)
│       ├── button/
│       ├── table/
│       ├── form/
│       └── navigation-menu/
├── layouts/
│   └── DefaultLayout.vue    # Shell with sidebars/rails
├── screens/
│   ├── TicketList.vue       # From ui TicketList
│   ├── TicketForm.vue       # From ui TicketForm
│   └── TicketDashboard.vue  # From ui TicketDashboard
├── router/
│   └── index.ts             # Generated routes + guards
├── stores/
│   ├── ui.ts                # Layout state (sidebar, etc.)
│   └── auth.ts              # RBAC integration
└── main.ts
```

## Reuse from Harmonia

| Harmonia Pattern | CICSC Usage |
|-----------------|-------------|
| `App.vue` layout shell | `DefaultLayout.vue` template |
| `stores/ui.ts` | Layout state (containers, sidebar) |
| `components/features/navigation/` | Navigation menu generation |
| `baseMenu.ts` | Navigation structure from `ui.navigation` |
| `router/index.ts` | Route generation with guards |
| `auth/store.ts` | RBAC integration |
| Component library | Default registry implementation |
| `useToast.ts` | Action feedback |

## Milestones

### BV1: Core IR UI Extension
- [x] BV1.1: Add UiSpecV0 to Core IR
- [x] BV1.2: Define layout primitives
- [x] BV1.3: Define navigation structure
- [x] BV1.4: Update IR validator

### BV2: Component Contract & Registry
- [x] BV2.1: JSON Schema component contract
- [x] BV2.2: Capability declaration system
- [x] BV2.3: Component registry format
- [x] BV2.4: Default shadcn-vue library setup

### BV3: UI Generator & Runtime
- [x] BV3.1: Layout shell generator
- [x] BV3.2: Navigation menu generator
- [x] BV3.3: Screen generator (table/form)
- [x] BV3.4: Dashboard generator

### BV4: Integration & Polish
- [x] BV4.1: Theme system (dark/light)
- [x] BV4.2: Toast/notification feedback
- [x] BV4.3: Auth integration (RBAC)
- [x] BV4.4: Router generation with guards
