import type { CoreIrV0, UiSpecV0, EntityTypeSpecV0 } from "../core/ir/types"

export function generateUiFromIr(ir: CoreIrV0): UiSpecV0 {
  const pages: Record<string, any> = {}
  const components: Record<string, any> = {}
  const theme: any = {}

  for (const [entityName, entity] of Object.entries(ir.types || {})) {
    const pageId = entityName.toLowerCase()
    
    components[`${pageId}-list`] = {
      kind: "table",
      entity: entityName,
      fields: Object.keys(entity.attrs || {}),
      actions: generateActions(entity),
    }

    components[`${pageId}-form`] = {
      kind: "form",
      entity: entityName,
      fields: Object.keys(entity.attrs || {}),
      actions: generateActions(entity),
    }

    components[`${pageId}-card`] = {
      kind: "card",
      entity: entityName,
      fields: Object.keys(entity.attrs || {}).slice(0, 5),
    }

    if (entity.states && entity.states.length > 1) {
      components[`${pageId}-kanban`] = {
        kind: "kanban-board",
        entity: entityName,
        states: entity.states,
      }
    }

    pages[pageId] = {
      path: `/${pageId}`,
      title: entityName,
      entity: entityName,
      layout: { kind: "list" },
      sections: [
        {
          id: `${pageId}-main`,
          components: [
            { component_id: `${pageId}-list` },
          ],
        },
      ],
    }

    pages[`${pageId}-new`] = {
      path: `/${pageId}/new`,
      title: `New ${entityName}`,
      entity: entityName,
      layout: { kind: "form" },
      sections: [
        {
          id: `${pageId}-form`,
          components: [
            { component_id: `${pageId}-form` },
          ],
        },
      ],
    }
  }

  return {
    version: 0,
    pages,
    components,
    theme: {
      primary_color: "#3b82f6",
      accent_color: "#8b5cf6",
      border_radius: 8,
    },
  }
}

function generateActions(entity: EntityTypeSpecV0): Array<{ id: string; label: string; command: string; style: string }> {
  const actions: Array<{ id: string; label: string; command: string; style: string }> = []
  
  if (entity.commands) {
    for (const [cmdName] of Object.entries(entity.commands)) {
      actions.push({
        id: `action-${cmdName.toLowerCase()}`,
        label: cmdName,
        command: cmdName,
        style: "primary",
      })
    }
  }

  return actions
}

export function generateVueComponents(ui: UiSpecV0): Record<string, string> {
  const components: Record<string, string> = {}

  for (const [pageId, page] of Object.entries(ui.pages)) {
    components[`Page${capitalize(pageId)}.vue`] = generatePageComponent(page, ui)
  }

  for (const [compId, comp] of Object.entries(ui.components)) {
    components[`Ui${capitalize(compId)}.vue`] = generateComponentTemplate(comp)
  }

  return components
}

function generatePageComponent(page: any, ui: UiSpecV0): string {
  const sections = page.sections?.map((s: any) => {
    const comps = s.components?.map((ref: any) => {
      const comp = ui.components?.[ref.component_id]
      return comp ? `<Ui${capitalize(ref.component_id)} />` : ""
    }).join("\n        ") || ""
    return `      <section id="${s.id}">\n        ${comps}\n      </section>`
  }).join("\n") || ""

  return `<template>
  <div class="page-${page.path}">
    <header>
      <h1>${page.title}</h1>
    </header>
${sections}
  </div>
</template>

<script setup lang="ts">
// Auto-generated from SPEC
</script>

<style scoped>
.page-${page.path} {
  padding: 1rem;
}
</style>
`
}

function generateComponentTemplate(comp: any): string {
  const kind = comp.kind
  
  switch (kind) {
    case "table":
      return generateTableComponent(comp)
    case "form":
      return generateFormComponent(comp)
    case "card":
      return generateCardComponent(comp)
    case "kanban-board":
      return generateKanbanComponent(comp)
    default:
      return `<template>
  <div class="ui-component ui-${kind}">
    <!-- ${kind} component -->
  </div>
</template>`
  }
}

function generateTableComponent(comp: any): string {
  const fields = comp.fields?.map((f: string) => `      <th>${capitalize(f)}</th>`).join("\n") || ""
  const rows = `      <tr v-for="item in items" :key="item.id">
        ${comp.fields?.map((f: string) => `<td>{{ item.${f} }}</td>`).join("\n        ") || ""}
      </tr>`
  
  return `<template>
  <table class="ui-table">
    <thead>
      <tr>
${fields}
      </tr>
    </thead>
    <tbody>
${rows}
    </tbody>
  </table>
</template>

<script setup lang="ts">
defineProps<{
  entity: string
  items: any[]
}>()
</script>

<style scoped>
.ui-table {
  width: 100%;
  border-collapse: collapse;
}
.ui-table th, .ui-table td {
  padding: 0.5rem;
  border: 1px solid #ddd;
}
</style>
`
}

function generateFormComponent(comp: any): string {
  const inputs = comp.fields?.map((f: string) => `      <div class="form-field">
        <label>${capitalize(f)}</label>
        <input v-model="form.${f}" type="text" />
      </div>`).join("\n") || ""
  
  const actions = comp.actions?.map((a: any) => `<button @click="submit('${a.command}')">${a.label}</button>`).join("\n        ") || ""

  return `<template>
  <form class="ui-form" @submit.prevent="handleSubmit">
${inputs}
    <div class="actions">
${actions}
    </div>
  </form>
</template>

<script setup lang="ts">
import { ref } from 'vue'

const props = defineProps<{
  entity: string
}>()

const emit = defineEmits(['submit'])

const form = ref({})

function submit(command: string) {
  emit('submit', { command, data: form.value })
}
</script>

<style scoped>
.ui-form {
  max-width: 500px;
}
.form-field {
  margin-bottom: 1rem;
}
.form-field label {
  display: block;
  margin-bottom: 0.25rem;
}
</style>
`
}

function generateCardComponent(comp: any): string {
  const fields = comp.fields?.map((f: string) => `    <p><strong>${capitalize(f)}:</strong> {{ item.${f} }}</p>`).join("\n") || ""

  return `<template>
  <div class="ui-card">
${fields}
  </div>
</template>

<script setup lang="ts">
defineProps<{
  item: any
}>()
</script>

<style scoped>
.ui-card {
  border: 1px solid #ddd;
  border-radius: 8px;
  padding: 1rem;
}
</style>
`
}

function generateKanbanComponent(comp: string): string {
  return `<template>
  <div class="ui-kanban">
    <div 
      v-for="state in states" 
      :key="state" 
      class="kanban-column"
    >
      <h3>{{ state }}</h3>
      <div class="cards">
        <div 
          v-for="item in itemsByState(state)" 
          :key="item.id" 
          class="kanban-card"
        >
          {{ item.id }}
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed } from 'vue'

const props = defineProps<{
  entity: string
  items: any[]
  states: string[]
}>()

function itemsByState(state: string) {
  return props.items?.filter(i => i.state === state) || []
}
</script>

<style scoped>
.ui-kanban {
  display: flex;
  gap: 1rem;
}
.kanban-column {
  flex: 1;
  background: #f5f5f5;
  padding: 0.5rem;
  border-radius: 4px;
}
.kanban-card {
  background: white;
  padding: 0.5rem;
  margin: 0.5rem 0;
  border-radius: 4px;
  box-shadow: 0 1px 2px rgba(0,0,0,0.1);
}
</style>
`
}

function capitalize(str: string): string {
  return str.charAt(0).toUpperCase() + str.slice(1)
}
