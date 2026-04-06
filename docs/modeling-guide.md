# Modeling Guide

How to think about, structure, and work with Abide specifications.

This guide covers the principles and patterns that emerge from using Abide. It's not a syntax reference (see [syntax-at-a-glance](syntax-at-a-glance.md)) or a tutorial (see [getting-started](getting-started.md)) — it's about how to approach the work.

---

## The two activities

When you write a spec, you're doing two distinct things:

1. **Exploring** — "What are the right concepts? How do they relate?" You're discovering your model. You sketch types and entities, run the checker, see what's possible, refine.

2. **Verifying** — "Does this model satisfy my requirements?" You've committed to a design and you're checking it holds under all conditions.

These feel different. Exploring is loose and creative. Verifying is precise and exhaustive. Abide supports both — you start by exploring structure, then add behavior and verification as the model matures.

You don't need to get it right the first time. Define some types. Run it. See what happens. Add a constraint. Run again. This back-and-forth is the normal workflow.

---

## Entities are data, systems are services

The most important structural decision: what's an entity vs what's a system.

**Entities** are the things in your domain — they have identity, fields, and state machines. Think database rows, domain objects, things you'd see in an ER diagram:

```abide
entity Order {
  id: Id
  status: OrderStatus = @Pending
  total: Real

  action confirm() requires status == @Pending {
    status' = @Confirmed
  }
}
```

**Systems** are the services that operate on entities — they're singletons with events. Think microservices, controllers, domain boundaries:

```abide
system Commerce {
  use Order

  event place_order(total: Real) {
    create Order { total = total }
  }

  event confirm_order(order_id: Id) {
    choose o: Order where o.id == order_id {
      o.confirm()
    }
  }
}
```

The split: entities hold state, systems hold behavior. An entity answers "what is this thing and what states can it be in?" A system answers "what operations are available and how do they coordinate?"

If you're wondering "should this be an entity or a system?" — ask yourself: "are there multiple instances of this, or just one?" Multiple → entity. One → system.

| Code concept | Abide construct |
|-------------|----------------|
| Database model, domain object | Entity (pooled, created/destroyed by events) |
| Service, controller, manager | System (singleton, orchestrates entities) |
| Business rule, computation | `fn` with contracts |
| Configuration, constants | `const` or `struct` |
| Data shape without identity | `enum` (sum type) or `struct` (product type) |

> **Side note:** You might think you need a "class" for something like a ProcessManager or CacheService. You don't — that's a system. Systems are singletons that orchestrate entities. If your "class" has internal state, model the state as an entity and the behavior as a system. The split feels unfamiliar if you come from OOP, but it's how spec languages work — and it makes verification much cleaner because state and behavior are separated.

---

## Types are your vocabulary

Before writing entities or systems, define the vocabulary of your domain. Enums, structs, and type aliases are cheap — make lots of them:

```abide
enum OrderStatus = Pending | Confirmed | Shipped | Delivered | Cancelled
enum Priority = Low | Medium | High | Critical
type Money = Int  // cents, not dollars — avoid floating point in specs
struct Address { street: String, city: String, zip: String }
```

Enums define finite state spaces. Structs group related data. Type aliases (`type Money = Int`) give meaningful names to built-in types. Together they describe the conceptual landscape before any behavior is added.

A well-typed spec catches mistakes at the structural level: if `Priority` and `OrderStatus` are different types, you can't accidentally compare them.

---

## Actions are state machines

Entity actions aren't methods — they're **guarded transitions**. Each action says: "IF these conditions hold, THEN these fields change."

```abide
action ship() requires status == @Confirmed {
  status' = @Shipped
}
```

The `requires` clause is a guard — the action can only fire when the guard is true. The body describes what changes. Fields not mentioned don't change (the frame condition is automatic).

This means an entity IS a state machine. The actions define the transitions, the `requires` clauses define the guards, and the field assignments define the effects. You can read the entity definition and immediately see every possible state transition.

> **Side note on primed notation:** `status'` (with a prime mark) means "the next-state value of status." This is TLA+ notation. It's declarative — you're saying what the next state looks like, not imperatively assigning a value. The distinction matters for verification: the checker can reason about both `status` (current) and `status'` (next) simultaneously.

---

## Events are the external interface

Events are what the outside world can trigger. They're defined in systems, and they invoke entity actions:

```abide
event freeze_account(account_id: Id)
  requires exists a: Account | a.id == account_id and a.status == @Active {
  choose a: Account where a.id == account_id {
    a.freeze()
  }
  // Revoke all sessions for this account
  for s: Session {
    s.revoke()
  }
}
```

Three primitives in event bodies:

- **`choose`** — select one entity matching a condition and operate on it
- **`for`** — operate on all entities of a type
- **`create`** — bring a new entity instance into existence

Events can call other systems' events for cross-service coordination: `Billing::charge(order.id)`.

> **In development — syntax subject to change:** `for` will be generalized to iterate over collection values (`for item in order.items { ... }`) and bounded ranges (`for i in 0..count { ... }`), not just entity pools.

---

## The verification ladder

Abide offers four levels of confidence, each stronger than the last:

### Scenes — "does this path work?"

Manual test cases. You set up a specific scenario and check the outcome:

```abide
scene deposit_success for Banking {
  given let a = one Account where a.status == @Active and a.balance == 1000
  when action dep = Banking::deposit(a, 500){one}
  then assert a.balance == 1500
}
```

Scenes are documentation that the checker validates. They answer: "here's an example of how the system should work."

### Verify — "does it hold for all behaviors?"

Bounded model checking. The checker explores ALL possible event orderings within a scope:

```abide
verify account_safety for Banking[0..500] {
  assert always (all a: Account | a.balance >= 0)
}
```

This says: "with up to 500 entities, try every possible event ordering. Does the balance ever go negative?" If yes, the checker gives you the exact event sequence that caused it.

> **Side note on scope:** The scope pre-allocates entity slots — like reserving seats. `Banking[0..500]` means "at most 500 entity instances can exist." The `create` keyword activates a slot. When all slots are active, no more can be created. This is how Alloy works under the hood — the scope IS the universe.

### Run and simulate *(in development — syntax subject to change)*

Per-entity-type scope gives finer control over the verification universe:

```abide
run safety_check ->
  Account[0..10], Session[0..20]
  for 50 {
  assert always (all a: Account | a.balance >= 0)
}
```

Hierarchical scope with `<-` expresses structural containment, eliminating unrealistic configurations:

```abide
run workflow_test ->
  Workflow[3] <- Node[1..4] <- Edge[derive],
  WorkflowRun[5] <- StepExecution[2..10]
  for 500 {
  assert always (all r: WorkflowRun | r.status == @Completed implies
    no s: StepExecution | s.run_id == r.id and s.status == @Active)
}
```

Simulation mode explores random traces for larger systems where exhaustive checking is too expensive:

```abide
simulate stress_test ->
  User[100], Order[1000], Payment[500]
  for 5000
  traces 200 {
  assert always (all o: Order | o.total >= 0)
}
```

Run 200 random traces of 5000 steps each. Not complete, but practical. Most real bugs show up in random traces.

### Theorem — "does it hold for all sizes?"

Unbounded proof. No scope limitation — the property holds for any number of entities:

```abide
theorem no_overdraft for Banking {
  show always (all a: Account | a.balance >= 0)
}
```

The solver attempts an inductive proof. If it succeeds, the property is guaranteed for all time and all entity counts. If it can't, you're told what's missing and can add lemmas to help.

> **Side note on theorem vs proof:** In Abide, `theorem` is the CLAIM — what you want to prove. `proof` (future) is the ARGUMENT — how you prove it. This follows mathematical convention: a theorem states the result, a proof demonstrates it. For now, the solver attempts the proof automatically. Later, `proof { }` blocks will let you guide the solver with intermediate steps.

---

## Start abstract, add detail

You don't need to write everything at once. Start with types and entities — just the structure:

```abide
enum OrderStatus = Pending | Confirmed | Shipped

entity Order {
  id: Id
  status: OrderStatus
}
```

Run the checker. See what instances exist. Does the state space look right? Are you missing a status? Then add actions:

```abide
entity Order {
  id: Id
  status: OrderStatus = @Pending

  action confirm() requires status == @Pending { status' = @Confirmed }
  action ship() requires status == @Confirmed { status' = @Shipped }
}
```

Then add a system. Then add verification. Each step adds detail without invalidating the previous work. This is the layered approach:

1. **Enums, structs, and entities** — "what exists?" (explore)
2. **Actions and events** — "what can happen?" (model behavior)
3. **Verify and scenes** — "is it correct?" (check properties)
4. **Theorems** — "is it provably correct?" (prove guarantees)

Most specs stop at layer 3. That's fine. Each layer is useful on its own.

---

## Predicates and properties are documentation

Name your constraints:

```abide
pred is_active(a: Account) = a.status == @Active
pred has_funds(a: Account, amount: Real) = a.balance >= amount

prop no_overdraft for Banking = always (all a: Account | a.balance >= 0)
```

Predicates (`pred`) are reusable boolean expressions — they give names to concepts. Properties (`prop`) are named assertions about the system — they're checked automatically by the checker.

Use predicates liberally. They make your verification readable:

```abide
// Hard to read
assert always (all a: Account | a.status != @Deleted implies a.balance >= 0)

// Easy to read
assert always (all a: Account | is_active(a) implies has_funds(a, 0))
```

---

## Use functions for computation

Pure functions (`fn`) compute values without side effects:

```abide
fn calculate_total(subtotal: Real, tax_rate: Real): Real =
  subtotal + (subtotal * tax_rate)

fn is_eligible(age: Int): Bool = age >= 18
```

Functions are great for business rules, derived values, and computations that multiple events share.

Functions cannot modify entity state — that's what actions are for. This separation is intentional: functions are pure (easy to verify), actions are stateful (need more care).

> **In development — syntax subject to change:** Functions will gain `requires`/`ensures` contracts, imperative block bodies with `var` and `while`, and termination measures via `decreases`. This enables Dafny-style algorithm verification within Abide.

---

## Collections model relationships

Use `Set`, `Seq`, and `Map` for entity relationships and structured data:

```abide
entity Workflow {
  id: Id
  name: String
  node_ids: Set<Id>
  variables: Map<String, String>
}
```

Update maps with the `[k := v]` syntax:

```abide
action set_variable(key: String, value: String) {
  variables' = variables[key := value]
}
```

Read with index syntax: `variables[key]`.

Build sets with comprehensions:

```abide
// All active accounts with positive balance
{ a: Account where a.status == @Active and a.balance > 0 }

// Just the balances
{ a.balance | a: Account where a.status == @Active }
```

---

## File organization

Abide doesn't enforce file structure, but convention helps:

| File pattern | Contents | Purpose |
|-------------|----------|---------|
| `*.ab` | Types, entities, systems, functions | Definitions — what the system IS |
| `*.spec.ab` | Verify blocks, scenes, predicates, properties | Verification — does it work? |
| `*.proof.ab` | Theorems, lemmas, axioms | Proofs — why does it work? |

Every file declares its module: `module Commerce` at the top. Multiple files can share a module. Use `use Commerce::*` to bring names into scope across modules.

For larger projects, separate structure from behavior from verification. For small specs, put everything in one file. The compiler doesn't care — it processes all constructs regardless of file extension.

---

## Common patterns

### The guard-and-dispatch pattern

When different behavior depends on data, use separate events with discriminating `requires` clauses:

```abide
event process_standard(order_id: Id)
  requires exists o: Order | o.id == order_id and o.priority == @Standard { ... }

event process_express(order_id: Id)
  requires exists o: Order | o.id == order_id and o.priority == @Express { ... }
```

The checker explores which event fires based on the entity state. You don't need if/else — the `requires` clauses handle dispatch.

### The coordinator pattern

Cross-system coordination through event calls:

```abide
system OrderFulfillment {
  use Order

  event fulfill(order_id: Id) {
    choose o: Order where o.id == order_id {
      o.ship()
    }
    Billing::finalize_payment(order_id: order_id)
    Notifications::send_shipped_email(order_id: order_id)
  }
}
```

One event triggers actions across multiple systems. The spec captures the coordination — if Billing and Notifications need to happen atomically with shipping, this event expresses that.

### The lifecycle pattern

Model entity creation, state transitions, and (optionally) destruction as a complete lifecycle:

```abide
system SessionManager {
  use Session

  event login(user_id: Id) {
    create Session {
      user_id = user_id
      status = @Active
    }
  }

  event logout(session_id: Id) {
    choose s: Session where s.id == session_id {
      s.expire()
    }
  }
}
```

The full lifecycle: create → transitions → terminal state. Scoped verification checks that the lifecycle is well-behaved.

---

## When you're stuck

If you can't figure out how to model something:

1. **Start with enums and structs.** What are the concepts? Name them. Don't worry about behavior yet.
2. **Ask "what changes?"** The things that change are entities. The things that cause change are events.
3. **Draw the state machine.** Entity actions ARE the state machine. If you can draw it, you can write it.
4. **Write a scene first.** A concrete example ("user signs up, creates an order, pays") often clarifies the abstract model.
5. **Check the FAQ.** Common modeling questions are answered in [faq.md](faq.md).
