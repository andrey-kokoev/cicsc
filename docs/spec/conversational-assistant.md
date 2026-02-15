# Conversational Spec Assistant - Design (BG1)

The Conversational Spec Assistant lowered the barrier to entry for non-programmers by guiding them through the creation of a CICSC Spec using natural language.

## Conversational Flow (BG1.1)

1. **Domain Discovery**: Ask "What system are we building?" (e.g., "A library system").
2. **Entity Discovery**: Identify the main "things" in that system ("Books, Members").
3. **State Discovery**: For each entity, ask "What are the different stages or statuses this thing can be in?"
4. **Attribute Discovery**: For each entity, ask "What information do we need to store about this?"
5. **Command Discovery**: Ask "What actions can people take on this thing?"
    - Link actions to state transitions (e.g., "When someone borrows a book, what happens to its status?").
6. **Confirmation**: Present a draft Spec summarize for the user to approve.

## Question Templates (BG1.2)

- **Entities**: "What are the main objects we need to track in your {domain}?"
- **States**: "What are the possible statuses a {entity} can have (e.g., New, Active, Closed)?"
- **Attributes**: "What specific details should we save for a {entity}? (e.g., name, price, date)"
- **Commands**: "What can someone do with a {entity} when it is in the {state} state?"
- **Transitions**: "When executing {command}, does the {entity} change into a new state?"

## Handling Ambiguity (BG1.3)

- **Vague nouns**: If the user says "People", ask "Is 'People' an entity like a User, or an actor who performs actions?"
- **Missing types**: If a user mentions a field "due date" but not the type, infer `time` and ask for confirmation.
- **Unreachable states**: If a state is defined but no command leads to it, flag it.

## Summary Engine (BG1.4)

A simple mapping that converts the internal state of the interview into a human-readable summary:
"Okay, I've got it. We are building a {domain}. We'll have {entities}. {entity1} starts as {initial_state} and can become {states} via {commands}."
