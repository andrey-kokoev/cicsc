import { KernelMemoryBackend, verifyHistoryAgainstIr } from "../../kernel/src/index"

const backend = new KernelMemoryBackend()
backend.append([
  {
    tenant_id: "t",
    entity_type: "Ticket",
    entity_id: "A",
    seq: 1,
    event_type: "created",
    payload: {},
    ts: 1,
    actor_id: "u",
  } as any,
])

const bundle: any = {
  core_ir: {
    version: 0,
    types: {
      Ticket: {
        id_type: "string",
        states: ["new", "open"],
        initial_state: "new",
        attrs: {},
        commands: {},
        reducer: {
          created: [{ set_state: { expr: { lit: { string: "open" } } } }],
        },
      },
    },
  },
}

const report = verifyHistoryAgainstIr({
  bundle,
  events: backend.readAll(),
  now: 2,
  actor: "u",
  intrinsics: {
    has_role: () => true,
    role_of: () => "user",
    auth_ok: () => true,
    constraint: () => true,
    len: () => 0,
    str: (v: any) => (v == null ? null : String(v)),
    int: () => null,
    float: () => null,
  },
})

console.log(JSON.stringify(report, null, 2))
