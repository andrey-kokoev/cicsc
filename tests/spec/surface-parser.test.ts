import { describe, it } from "node:test"
import assert from "node:assert/strict"
import { parseDSL } from "../../spec/parse-dsl"

describe("Surface DSL Parser", () => {
  it("parses a simple entity with attributes", () => {
    const input = `
entity Ticket:
  states: [Open, Closed]
  attr title
  attr priority: enum [P0, P1]
    `;
    const spec = parseDSL(input);
    assert.ok(spec.entities.Ticket);
    assert.equal(spec.entities.Ticket.initial, "Open"); // default initial sugar
    assert.equal(spec.entities.Ticket.attributes!.title.type, "string"); // default type sugar
  });

  it("parses commands with implicit emits", () => {
    const input = `
entity Ticket:
  states: [Open, Closed]
  command Resolve:
    when state is Open
    `;
    const spec = parseDSL(input);
    const cmd = spec.entities.Ticket.commands!.Resolve;
    assert.equal(cmd.emit.length, 1);
    assert.equal(cmd.emit[0].type, "Resolveed");
  });

  it("parses complex constraints and views", () => {
    const input = `
entity Ticket:
  states: [Open, Closed]
  attr priority: string

view BigView:
  on Ticket
  where state is Open
  order_by priority desc

constraint NoEmptyTitle:
  on Ticket
  assert title is not empty
    `;
    const spec = parseDSL(input);
    assert.ok(spec.views!.BigView);
    assert.ok(spec.constraints!.NoEmptyTitle);
  });
});
