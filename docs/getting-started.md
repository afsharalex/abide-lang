# Getting Started

Abide is a specification language for stateful systems, workflows, and verification.

This guide uses the syntax that the current compiler accepts on `master`:
- store-backed systems: `system Commerce(orders: Store<Order>)`
- public command surface plus executable `step` clauses
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

system Commerce(orders: Store<Order>) {

  command create_order(total: real)

  step create_order(total: real)
    requires total > 0 {
    create Order {
      total = total
    }
  }

  command pay(order: Order)

  step pay(order: Order)
    requires order.status == @Pending {
    order.mark_paid()
  }

  command ship(order: Order)

  step ship(order: Order)
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
    store orders: Order[1..1]
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

## What the pieces mean

- `entity` declares stateful domain objects with fields and actions.
- `system ... (orders: Store<Order>)` declares a system over a bounded pool of entities.
- `command` declares the public API surface of the system.
- `step` gives an executable implementation clause for a command.
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

system Commerce(orders: Store<Order>) {
  command create_order(total: real)
  step create_order(total: real) { create Order { total = total } }
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
abide simulate order.ab --steps 10
```

## Next guides

- [Syntax at a Glance](syntax-at-a-glance.md)
- [Core Concepts](core-concepts.md)
- [CLI Reference](cli.md)
- [QA Language](qa-language.md)
