# Getting Started

> Abide is under heavy development. The syntax and semantics will change frequently. We will announce when an alpha release with solver backend support is available.

## Prerequisites

- Rust toolchain (stable) — install via [rustup.rs](https://rustup.rs)

## Build

```sh
git clone https://github.com/afsharalex/abide-lang.git
cd abide-lang/compiler
cargo build --release
```

The binary is at `target/release/abide`.

## Write Your First Spec

Create a file called `order.abide`:

```abide
enum OrderStatus = Pending | Paid | Shipped

entity Order {
  id: Id
  status: OrderStatus = @Pending
  total: Real

  action pay() requires status == @Pending requires total > 0 {
    status' = @Paid
  }

  action ship() requires status == @Paid {
    status' = @Shipped
  }
}

system Commerce {
  use Order

  event place_order(o: Order) requires o.status == @Pending {
    o.pay()
  }
}
```

## Check It

```sh
abide parse order.abide
```

If the spec parses correctly, the compiler prints the AST. If there's a syntax error, it points to the offending line.

To verify the spec (induction, IC3/PDR, and bounded model checking):

```sh
abide verify order.abide
```

## What Just Happened

You defined:

- An **enum** (`OrderStatus`) — a sum type with three states
- An **entity** (`Order`) — a stateful domain object with fields and defaults
- Two **actions** (`pay`, `ship`) — guarded state transitions using primed notation (`status' = @Paid` means "the next value of status is Paid")
- A **system** (`Commerce`) — a boundary that composes entities and defines events
- An **event** (`place_order`) — an externally triggered action with a precondition

The `@` prefix marks state atoms (`@Pending`, `@Paid`). The prime notation (`'`) distinguishes current state from next state — this is how Abide expresses state transitions without mutation.

## Add Verification

Append this to your file:

```abide
verify order_lifecycle for Commerce[0..50] {
  assert always (all o: Order |
    o.status == @Shipped implies o.total > 0)
}

scene successful_payment for Commerce {
  given let o = one Order where o.status == @Pending and o.total == 100
  when action p = Commerce::place_order(o) { one }
  then assert o.status == @Paid
}
```

The `verify` block asks the checker to explore up to 50 steps of the Commerce system. It tries induction and IC3/PDR first (unbounded proof), then falls back to bounded model checking. Run `abide verify <file>` to execute it.

The `scene` block constructs a concrete scenario: given an order in a specific state, when a specific event fires, then a specific outcome holds. Scenes are existential witnesses — they demonstrate that a behavior is possible.

Abide also supports collection-typed fields (`Map<K,V>`, `Set<T>`, `Seq<T>`) with map update (`m[k := v]`), index access (`m[k]`), set comprehension (`{ x: T where P(x) }`), and cardinality (`#S`). These are verified using Z3's array theory.

Properties declared with `prop` are automatically verified — declaring a property IS asserting it must hold:

```abide
prop order_safety for Commerce =
  always all o: Order | o.total >= 0
```

## Organize with Modules

As specs grow, split them into multiple files using the module system:

```abide
// types.abide
module Commerce

pub enum OrderStatus = Pending | Paid | Shipped

pub entity Order {
  id: Id
  status: OrderStatus = @Pending
  total: Real

  action pay() requires status == @Pending {
    status' = @Paid
  }
}
```

```abide
// system.abide
module Commerce

use Commerce::Order
use Commerce::OrderStatus

system Commerce {
  use Order

  event place_order(o: Order) requires o.status == @Pending {
    o.pay()
  }
}
```

```abide
// spec.abide
module Spec

use Commerce::*

verify order_safety for Commerce[0..50] {
  assert always (all o: Order | o.status == @Shipped implies o.total > 0)
}
```

Verify all files together:

```sh
abide verify types.abide system.abide spec.abide
```

Key module system concepts:
- `module Name` at the top of each file declares which module it belongs to
- `pub` marks declarations visible to other modules (private by default)
- `use Module::Name` imports a specific declaration; `use Module::*` imports all public names
- `use Module::Name as Alias` provides a local alias
- `include "file.abide"` includes a file's contents into the current module
- Systems and events are always public; entity fields are always private

## Explore with the REPL

The REPL lets you interactively explore your specs:

```sh
$ abide repl commerce/
Loaded 2 entities, 1 system

abide> /qa
qa> ask reachable Order.status -> @Shipped
true
qa> ask terminal Order.status
@Shipped, @Cancelled
qa> /quit
```

Switch between Abide mode (write definitions) and QA mode (query the spec) with `/qa` and `/abide`. See the [REPL guide](repl.md) for details.

## Run QA Scripts

Automate structural checks with `.qa` scripts:

```sh
$ abide qa checks.qa
  PASS: assert reachable Order.status -> @Shipped
  PASS: assert not cycles Order.status

=== QA: 2 passed, 0 failed (2 executed) ===
```

See the [QA Language](qa-language.md) guide.

## Verify Algorithms

Beyond system-level properties, Abide verifies function contracts. Attach `requires`, `ensures`, and `decreases` to functions with imperative bodies:

```abide
fn gcd(a: Int, b: Int): Int
  requires a > 0
  requires b >= 0
  ensures result > 0
  decreases b
{
  var x = a
  var y = b
  while y != 0
    invariant x > 0
    invariant y >= 0
    decreases y
  {
    var temp = y
    y = x % y
    x = temp
  }
  x
}
```

`abide verify` automatically proves that the body satisfies the postcondition, that while-loop invariants are maintained, and that recursive calls decrease the termination measure. Preconditions are checked at every call site.

Refinement types provide a shorthand — `fn f(x: Int { $ > 0 })` is equivalent to `fn f(x: Int) requires x > 0`, and type aliases like `type Positive = Int { $ > 0 }` work the same way.

## Next Steps

- [Syntax at a Glance](syntax-at-a-glance.md) — quick reference for all constructs
- [Core Concepts](core-concepts.md) — the five specification layers
- [REPL](repl.md) — interactive specification exploration
- [QA Language](qa-language.md) — structural analysis queries
- [Examples](examples.md) — more specs to learn from
