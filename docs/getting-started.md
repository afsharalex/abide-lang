# Getting Started

Abide is a specification language for stateful systems, workflows, and verification.

This guide uses the syntax that the current compiler accepts on `master`:
- store-backed systems: `system Commerce(orders: Store<Order>[..4])`
- public commands and queries, with inline command bodies where needed
- verification blocks with explicit `assume { store ...; let ... }`

## Build

```sh
git clone https://github.com/afsharalex/abide-lang.git
cd abide-lang
cargo build
```

The binary will be at `target/debug/abide`.

## First spec

Create `order.ab`:

```abide
module OrderDemo

enum OrderStatus = Pending | Paid | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0

  action mark_paid()
    requires status == @Pending
    requires total > 0 {
    status' = @Paid
  }

  action ship()
    requires status == @Paid {
    status' = @Shipped
  }
}

system Commerce(orders: Store<Order>[..4]) {
  command create_order(total: real)
    requires total > 0 {
    create Order {
      total = total
    }
  }

  command pay(order: Order)
    requires order.status == @Pending {
    order.mark_paid()
  }

  command ship(order: Order)
    requires order.status == @Paid {
    order.ship()
  }
}
```

## Parse it

```sh
abide parse order.ab
```

If parsing succeeds, Abide prints the AST. If it fails, the diagnostic points at the rejected syntax.

## Verify it

Append:

```abide
verify shipped_orders_have_value {
  assume {
    store orders: Order[0..4]
    let commerce = Commerce { orders: orders }
  }
  assert always all o: Order | o.status == @Shipped implies o.total > 0
}

scene payment_then_shipping {
  given {
    store orders: Order[1]
    let commerce = Commerce { orders: orders }
    let o = one Order in orders where o.total == 25
  }
  when {
    commerce.pay(o)
    commerce.ship(o)
  }
  then {
    assert o.status == @Shipped
  }
}
```

Then run:

```sh
abide verify order.ab
```

## Rel checks

Abide can check finite relation expressions directly. `Rel<T...>` is the
first-class collection type for finite tuple relations. Relation operations
are associated functions on `Rel`, such as `Rel::join(left, right)`.
Pipeline form is also supported when the operation remains fully qualified:
`left |> Rel::join(right)`.

```abide
enum OrderStage = Draft | Paid | Shipped
enum FulfillmentPhase = Open | Complete
enum HandlingLane = Manual | Automated

verify stage_lanes {
  assert Rel((@Draft, @Open), (@Paid, @Open), (@Shipped, @Complete))
    |> Rel::join(Rel((@Open, @Manual), (@Complete, @Automated)))
    == Rel((@Draft, @Manual), (@Paid, @Manual), (@Shipped, @Automated))
}

verify lifecycle_reachability {
  assert Rel::reach(
    Rel((@Draft, @Paid), (@Paid, @Shipped))
  ) == Rel(
    (@Draft, @Draft),
    (@Paid, @Paid),
    (@Shipped, @Shipped),
    (@Draft, @Paid),
    (@Paid, @Shipped),
    (@Draft, @Shipped)
  )
}
```

Run it the same way:

```sh
abide verify relations.ab
```

For a failing relation equality or subset, verify output includes the computed
tuple sets that caused the counterexample.

Store-backed relation comprehensions build relations from finite entity pools:

```abide
assert always Rel((o, c) | o: Order in orders, c: Customer in customers where o.customer_id == c.id)
  <= (Rel::field(orders, Order::customer_id) |> Rel::join(Rel::transpose(Rel::field(customers, Customer::id))))
```

They can also be composed with reachability operations:

```abide
assert always Rel((a, c) | a: Node in nodes, c: Node in nodes where a.id == @NodeA and c.id == @NodeC)
  <= Rel::reach(Rel((left, right) | left: Node in nodes, right: Node in nodes where left.next_id == right.id))
```

## Collection comprehensions

Set comprehensions can filter and map finite collection sources:

```abide
entity Dummy {
  id: identity
}

system Fixture(dummies: Store<Dummy>) {
  command noop() { }
}

verify collection_examples {
  assume {
    store dummies: Dummy[0..1]
    let fixture = Fixture { dummies: dummies }
  }

  assert { x * 2 | x in Set(1, 2, 3) where x > 1 } == Set(4, 6)

  assert { amount | amount in Seq(10.0, 25.0, 50.0) where amount >= 25.0 }
    == Set(25.0, 50.0)
}
```

See [`examples/collections.ab`](../examples/collections.ab) for a complete runnable file.

## What the pieces mean

- `entity` declares stateful domain objects with fields and actions.
- `system ... (orders: Store<Order>[..4])` declares a system over a finite pool of entities.
- Store bounds can be exact (`[1]`), ranged (`[1..4]`), or at-most (`[..4]`).
- The lower bound is the initial active population. `[1..4]` starts with one active entity and can grow to four; `[..4]` starts empty.
- `command` declares a public system operation and may include its body inline.
- `verify` checks universal properties.
- `scene` checks existential witness scenarios.

Systems are defined over explicit store pools, and verification assumptions instantiate those pools directly.

## Modules

Split larger specs into multiple files:

```abide
// types.ab
module Commerce

enum OrderStatus = Pending | Paid | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0
}
```

```abide
// system.ab
module Commerce

use Commerce::Order
use Commerce::OrderStatus

system Commerce(orders: Store<Order>[..4]) {
  command create_order(total: real) { create Order { total = total } }
}
```

```abide
// checks.ab
module CommerceChecks

use Commerce::*

verify positive_totals {
  assume {
    store orders: Order[0..4]
    let commerce = Commerce { orders: orders }
  }
  assert always all o: Order | o.total >= 0
}
```

Run them together:

```sh
abide verify types.ab system.ab checks.ab
```

## Interactive tools

REPL:

```sh
abide repl .
```

QA scripts:

```sh
abide qa checks.qa -f .
```

Simulation:

```sh
abide run order.ab --steps 10
```

## Next guides

- [Syntax at a Glance](syntax-at-a-glance.md)
- [Core Concepts](core-concepts.md)
- [CLI Reference](cli.md)
- [QA Language](qa-language.md)
