# Syntax at a Glance

Quick reference for all Abide constructs. Each section shows a minimal example, a brief explanation, and a stability tag.

**Stability tags:** `Stable` = unlikely to change. `Evolving` = may change in syntax or semantics. `Planned` = designed but not yet implemented.

---

### Enums

```abide
enum OrderStatus = Pending | Paid | Shipped | Cancelled
```

Sum types. Enums define the vocabulary of state with named constructors.

`Stable`

---

### Structs

```abide
struct Address { street: String, city: String }
```

Product types with named fields. Structs group related data.

`Stable`

---

### Type Aliases

```abide
type Price = Int
```

Type aliases give a new name to an existing type.

`Stable`

---

### Algebraic Data Types

```abide
enum Shape =
  Circle { radius: Real }
  | Rectangle { width: Real, height: Real }
  | Point
```

Sum types with record variants. Each variant can carry different fields.

`Stable`

---

### Entities

```abide
entity Order {
  id: Id
  status: OrderStatus = @Pending
  total: Real

  action pay() requires status == @Pending requires total > 0 {
    status' = @Paid
  }
}
```

Stateful domain objects with identity. Fields have types and optional defaults. Actions define guarded state transitions. `status' = @Paid` means "the next value of status is Paid."

`Stable`

---

### State Atoms

```abide
@Pending                   // simple atom
@OrderStatus::Paid         // qualified atom
```

The `@` prefix marks state and constructor values. `::` is scope resolution for qualified references.

`Stable`

---

### Primed Notation

```abide
action withdraw(amount: Real) requires balance >= amount {
  balance' = balance - amount
}
```

`balance` is the current (pre-state) value. `balance'` is the next (post-state) value. Fields not mentioned in the action body are unchanged (inertia).

`Stable`

---

### Contracts

```abide
action deposit(amount: Real)
  requires amount > 0
  requires status == @Active
  ensures balance' == balance + amount {
  balance' = balance + amount
}
```

`requires` = precondition (must be true to execute). `ensures` = postcondition (must be true after execution). Contracts attach to actions, events, and functions.

`Stable`

---

### Systems and Events

```abide
system Banking {
  use Account

  event deposit(a: Account, amount: Real)
    requires amount > 0 {
    a.deposit(amount)
  }
}
```

Systems compose entities and define events. Events are externally triggered operations that invoke entity actions. `use` declares which entities the system operates on.

`Stable`

---

### Entity Reference Parameters

```abide
action transfer_out[to: Account](amount: Real) requires balance >= amount {
  balance' = balance - amount
}
```

Square brackets `[to: Account]` declare entity reference parameters — references to other entity instances that the action can read or modify.

`Stable`

---

### Predicates

```abide
pred is_active(a: Account) = a.status == @Active
pred has_funds(a: Account, amount: Real) = a.balance >= amount
```

Named boolean expressions. Reusable in guards, properties, and verification blocks.

`Stable`

---

### Properties

```abide
prop no_negative_balances = all a: Account | a.balance >= 0
prop frozen_stable for Account = always (status == @Frozen implies status' == @Frozen)
```

Named assertions about the system. Global (`prop name = ...`) or scoped to an entity (`prop name for Entity = ...`).

`Stable`

---

### Pure Functions

```abide
fn max(a: Int, b: Int): Int = if a > b then a else b
fn risk_score(t: Transfer): Real = sorry
```

Named pure functions. `= expr` form for single expressions. `sorry` stubs a function body that will be filled in later.

`Stable`

---

### Constants

```abide
const MAX_WITHDRAWAL = 10000
const OVERDRAFT_LIMIT = 500
```

Named compile-time values. Used in guards, assertions, and expressions.

`Stable`

---

### Verify Blocks

```abide
verify no_overdraft for Banking[0..500] {
  assert always (all a: Account | a.balance >= 0)
  assert always (all a: Account |
    a.status == @Closed implies a.balance == 0)
}
```

Bounded model checking. The solver explores up to 500 steps of the Banking system and checks all assertions on every reachable state.

`Evolving`

---

### Scenes

```abide
scene successful_deposit for Banking {
  given let a = one Account where a.status == @Active and a.balance == 1000
  when action dep = Banking::deposit(a, 500) { one }
  then assert a.balance == 1500
}
```

Existential witnesses. Given initial conditions, when specific events fire, then specific outcomes hold. Scenes demonstrate that a behavior is possible.

`Evolving`

---

### Theorems, Lemmas, and Axioms

```abide
lemma frozen_blocks_transactions {
  all a: Account | all t: Transfer |
    a.status == @Frozen and t.from_account == a.id implies
      t.status != @Executed
}

theorem frozen_account_safety for Compliance, Banking
  invariant frozen_accounts_stable {
  show always (all a: Account |
    a.status == @Frozen implies a.balance' == a.balance)
}

axiom transfer_preserves_total {
  all a: Account | all b: Account |
    a.balance + b.balance == a.balance' + b.balance'
}
```

`lemma` = reusable proof building block. `theorem` = unbounded verification with invariants and `show` steps. `axiom` = assumed truth without proof (trusted assertion). Proof backends are under evaluation.

`Evolving`

---

### Match Expressions

```abide
fn describe(s: Shape): String =
  match s {
    Circle { radius: r } if r > 100 => "large circle"
    Circle { .. } => "circle"
    Rectangle { width: w, height: h } if w == h => "square"
    Shipped | Cancelled => "done"
    _ => "unknown"
  }
```

Pattern matching with destructuring, guards (`if`), or-patterns (`|`), rest patterns (`..`), and wildcards (`_`).

`Stable`

---

### Temporal Operators

```abide
always (all a: Account | a.balance >= 0)         // safety — holds on every state
eventually (exists o: Order | o.status == @Shipped)  // liveness — holds on some future state
a.status == @Frozen implies a.balance' == a.balance  // implication
```

`always` = on every reachable state (LTL box). `eventually` = on some future state (LTL diamond). `implies` = logical implication.

`Stable`

---

### Composition and Sequencing

```abide
submit -> pay -> ship             // temporal sequence (ordered steps)
deposit & update_log              // same-step (both happen simultaneously)
route_a | route_b                 // unordered composition (either order)
route_a || route_b                // concurrent composition
approve ^| reject                 // exclusive composition (exactly one)
x |> validate |> process          // pipe operator
```

`->` = temporal sequence (A then B). `&` = same-step. `|` = unordered. `||` = concurrent. `^|` = exclusive (one or the other, not both). `|>` = pipe (value flows left to right).

`Evolving`

---

### Quantifiers

```abide
all a: Account | a.balance >= 0             // universal
exists o: Order | o.status == @Paid          // existential
some a: Account | is_active(a)              // at least one
no a: Account | a.balance < 0               // none
one o: Order | o.status == @Pending          // exactly one
lone t: Transfer | t.status == @Pending      // at most one
```

Set quantifiers with formal semantics. `all`/`exists` are standard logical quantifiers. `some`/`no`/`one`/`lone` are cardinality quantifiers from Alloy.

`Stable`

---

### Sorry and Todo

```abide
fn calculate_risk(o: Order): Real = sorry
fn validate_address(a: Address): Bool = todo
```

`sorry` = "trust me, this is valid" (silent, for deliberate stubs). `todo` = "this is unfinished" (compiler warns). Both compile and act as valid expressions of any type.

`Stable`
