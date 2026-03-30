# Core Concepts

Abide organizes specification into five layers. Each builds on the previous. You work top-down: define structure, add behavior, assert temporal properties, verify algorithms, then prove deep guarantees.

Most projects only need the first three layers. Layers 4 and 5 are for when you need stronger guarantees than bounded checking provides.

---

## Layer 1: Structural Modeling

Define the vocabulary of your domain.

**Types** name the concepts:

```abide
enum OrderStatus = Pending | Confirmed | Shipped | Delivered | Cancelled
enum Currency = USD | EUR | GBP
struct Address { street: String, city: String, zip: String }
```

Enums (`enum`) define finite state spaces. Structs (`struct`) group related data. Algebraic data types combine both:

```abide
enum DosageForm =
  Tablet { mg: Int }
  | Liquid { ml: Int }
  | Injection { dose_mg: Int, route: String }
```

**Entities** are the stateful objects in your domain — things with identity that change over time:

```abide
entity Account {
  id: Id
  balance: Real
  status: AccountStatus = @Active
  currency: Currency = @USD
}
```

Fields have types, optional defaults, and state atom initializers (`@Active`). The `@` prefix marks state values — these are the vocabulary of your state space.

At this layer, you're answering: *"What things exist in my system, and what states can they be in?"*

---

## Layer 2: Behavioral Modeling

Define how things change.

**Actions** are guarded state transitions on entities:

```abide
entity Account {
  // ...fields...

  action deposit(amount: Real)
    requires status == @Active
    requires amount > 0
    ensures balance' == balance + amount {
    balance' = balance + amount
  }

  action freeze()
    requires status == @Active {
    status' = @Frozen
  }
}
```

The key notation:
- `requires` = precondition. The action can only execute when this is true.
- `ensures` = postcondition. This must be true after execution.
- `balance'` = the **next-state** value of `balance`. Unprimed `balance` is the **current** value.
- Fields not mentioned in the body don't change (inertia — the frame problem is handled automatically).

**Systems** compose entities and define events:

```abide
system Banking {
  use Account

  event deposit(a: Account, amount: Real)
    requires amount > 0 {
    a.deposit(amount)
  }

  event freeze_account(a: Account) {
    a.freeze()
  }
}
```

Events are the external interface — what the outside world can trigger. They invoke entity actions. Systems can reference multiple entities and coordinate between them.

**Predicates and properties** name reusable constraints:

```abide
pred is_active(a: Account) = a.status == @Active
pred has_funds(a: Account, amount: Real) = a.balance >= amount

prop no_overdraft = all a: Account | a.balance >= 0
```

Predicates are boolean expressions. Properties are assertions about the system — they can be used in verification and as documentation of invariants.

At this layer, you're answering: *"What can happen, under what conditions, and what must always be true?"*

---

## Layer 3: Temporal Modeling

Check properties across time.

**Verify blocks** use bounded model checking — the solver systematically explores event sequences up to a given depth:

```abide
verify account_safety for Banking[0..500] {
  assert always (all a: Account |
    a.status == @Frozen implies a.balance' == a.balance)

  assert always (all a: Account |
    a.status == @Closed implies a.balance == 0)
}
```

`always` means "on every reachable state." The solver tries every possible interleaving of events up to 500 steps. If any interleaving violates an assertion, it reports a counterexample trace showing exactly which events led to the violation.

**Scene blocks** are existential witnesses — they show that a specific behavior is possible:

```abide
scene successful_deposit for Banking {
  given let a = one Account where a.status == @Active and a.balance == 1000
  when action dep = Banking::deposit(a, 500) { one }
  then assert a.balance == 1500
}

scene cannot_withdraw_from_frozen for Banking {
  given let a = one Account where a.status == @Frozen and a.balance == 1000
  when action wd = Banking::withdraw(a, 100) { no }
  then assert a.balance == 1000
}
```

Scenes have three parts:
- `given` — set up initial conditions
- `when` — fire specific events (with cardinality: `one` = exactly once, `no` = must not be possible)
- `then` — assert outcomes

**Temporal operators** express properties over time:

```abide
always (P)               // P holds on every reachable state (safety)
eventually (P)           // P holds on some future state (liveness)
P implies Q              // if P then Q (logical implication)
P -> Q                   // P is followed by Q (temporal sequence)
```

**Composition operators** express how events relate to each other:

```abide
submit -> pay -> ship        // temporal sequence — ordered steps
deposit & update_log         // same-step — both happen simultaneously
route_a | route_b            // unordered — either order is valid
route_a || route_b           // concurrent — happen in parallel
approve ^| reject            // exclusive — exactly one happens, not both
```

These let you express complex event relationships: "submit must happen before pay, which must happen before ship" (`->`), "deposit and logging happen atomically" (`&`), "the system either approves or rejects, never both" (`^|`).

**Bounded vs. unbounded checking:**

`verify` blocks with bounds (`[0..500]`) will use bounded model checking — the solver explores finite depth. For many common safety properties, the solver will also attempt to **discharge them as unbounded proofs automatically** when the property is inductive or the state space is finite. When automatic unbounded checking fails, `theorem` and `lemma` blocks (Layer 5) provide the escape hatch to external proof backends. *(Solver backend in development.)*

**Interactive exploration** *(planned)* — the [REPL](repl.md) and [QA language](qa-language.md) let you explore specifications interactively:

```
$ abide repl commerce/
abide> /qa
qa> ask reachable Order.status -> @Shipped
true
qa> explain path Order.status @Pending -> @Shipped
@Pending -> submit -> @Confirmed -> ship -> @Shipped
qa> assert not cycles Order.status
PASS
```

The QA language answers structural questions about your spec instantly — reachability, terminal states, transition paths, cycles — using graph analysis on the precomputed FlowModel, no solver needed. The REPL lets you experiment with definitions against a live universe without modifying source files.

A planned **visual analyzer** will provide graphical state machine visualization, interactive transition exploration, and simulation playback.

At this layer, you're answering: *"Does my system behave correctly across all possible execution paths?"*

---

## Layer 4: Algorithm Verification *(Partially Implemented)*

Verify function and algorithm correctness.

Beyond system-level properties, some specifications need to verify that a specific algorithm is correct — that a sorting function actually sorts, that a routing algorithm finds the shortest path, that a cryptographic operation preserves certain invariants.

**Function contracts** are implemented: `requires`, `ensures`, and `decreases` clauses attach to `fn` declarations. Functions with contracts use the `{ body }` form:

```abide
fn gcd(a: Int, b: Int): Int
  requires a > 0
  requires b >= 0
  ensures result > 0
  decreases b
{
  match b {
    _ if b == 0 => a
    _ => gcd(b, a % b)
  }
}
```

- `requires` = precondition (must be Bool)
- `ensures` = postcondition (must be Bool, `result` refers to the return value)
- `decreases` = termination measure for recursive functions (must be Int, comma-separated for lexicographic tuples, `*` to skip checking)

**Imperative bodies** are planned for v0.2: `var` for mutable locals, `while` loops with `invariant` and `decreases`, `if`/`else` expressions:

```abide
// Planned syntax — not yet implemented

fn gcd_imperative(a: Int, b: Int): Int
  requires a > 0 and b > 0
  ensures result > 0 {
  var x = a
  var y = b
  while y != 0
    invariant x > 0 and y >= 0
    decreases y {
    var temp = y
    y = x % y
    x = temp
  }
  x
}
```

**Refinement types** will constrain values at the type level:

```abide
// Planned syntax — not yet implemented

type Positive = Int{$ > 0}
type Probability = Real{$ >= 0.0 and $ <= 1.0}

fn clamp(lo: Int, hi: Int{$ > lo}, x: Int): Int{$ >= lo and $ <= hi}
```

At this layer, you're answering: *"Is this specific algorithm correct?"*

---

## Layer 5: Proof Escape Hatch *(Planned)*

Prove properties beyond what automated checking can handle.

> This layer is designed but not yet fully implemented. The theorem/lemma syntax exists; backend integration is under evaluation.

The solver will attempt to discharge unbounded properties automatically where possible — many safety properties over finite state spaces or with inductive structure can be proved without human intervention. When the solver can't find a proof automatically, Abide provides an escape hatch to dependent type theory backends (**Agda**, **Lean 4**, or **Rocq** — under evaluation) where you write the proof yourself.

**Lemmas** are reusable proof building blocks:

```abide
lemma frozen_blocks_transactions {
  all a: Account | all t: Transfer |
    a.status == @Frozen and t.from_account == a.id implies
      t.status != @Executed
}
```

**Theorem blocks** declare unbounded invariants with proof steps:

```abide
theorem frozen_account_safety for Compliance, Banking
  invariant frozen_accounts_stable {
  show always (all a: Account |
    a.status == @Frozen implies a.balance' == a.balance)
}
```

For proofs that exceed what Abide can express directly, the planned approach is to export proof obligations to an external backend — **Agda**, **Lean 4**, or **Rocq** (under evaluation). The external prover produces a certificate that Abide trusts.

```abide
// Planned syntax — not yet implemented

proof module TransferSafety {
  theorem balance_preserved :
    forall (a b : Account) (amount : Real).
      a.balance + b.balance == a.balance' + b.balance'
  // proof in "proofs/balance.agda"
}
```

At this layer, you're answering: *"Can I get a mathematical guarantee, not just bounded confidence?"*

---

## How the Layers Compose

A typical project uses layers incrementally:

1. **Start with structure.** Define your entities, enums, and structs. Get the vocabulary right.
2. **Add behavior.** Write actions with guards. Define system events. This is where most of the work happens.
3. **Assert properties.** Write verify blocks to check invariants. Write scenes to validate scenarios. The solver finds bugs you didn't think of.
4. **Verify critical algorithms** *(when needed)*. If a function needs correctness guarantees beyond "the types check," add contracts and loop invariants.
5. **Prove deep properties** *(when needed)*. If bounded checking isn't enough, export to a proof backend.

Most specifications never need layers 4 and 5. The first three layers cover system-level correctness — the kind of bugs that cause outages, data corruption, and compliance violations.
