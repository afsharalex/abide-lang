# Syntax at a Glance

This is a current quick reference for the syntax accepted by the compiler on `master`.

## Modules

```abide
module Commerce
include "billing.ab"
use Commerce::Order
use Commerce::* as C
```

## Types

```abide
enum OrderStatus = Pending | Paid | Shipped

struct Address {
  street: string
  city: string
}

type Positive = int { $ > 0 }
```

## Entities and actions

```abide
entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0

  action mark_paid()
    requires status == @Pending
    requires total > 0 {
    status' = @Paid
  }
}
```

## Systems

```abide
system Commerce(orders: Store<Order>[..8]) {
  command pay(order: Order)
    requires order.status == @Pending {
    order.mark_paid()
  }

  query payable(order: Order) =
    order.status == @Pending and order.total > 0

  pred non_negative(order: Order) =
    order.total >= 0
}
```

Notes:
- `Store<T>` constructor params are the current entity-pool surface.
- Store constructor params may carry finite bounds: `Store<Order>[N]`, `Store<Order>[lo..hi]`, or `Store<Order>[..hi]`.
- `command` declares the public API and may carry its executable body inline.
- `query` is public and pure.
- `pred` is internal and pure.

## Verification

```abide
verify order_safety {
  assume {
    store orders: Order[0..8]
    let commerce = Commerce { orders: orders }
    fair Commerce::pay
  }
  assert always all o: Order | o.total >= 0
}
```

## Theorems, lemmas, axioms

```abide
lemma positive_totals {
  all o: Order | o.total >= 0
}

theorem shipped_orders_have_value =
  always all o: Order | o.status == @Shipped implies o.total > 0

axiom external_fact = true by "proofs/external.agda"
```

## Scenes

```abide
scene successful_payment {
  given {
    store orders: Order[1]
    let commerce = Commerce { orders: orders }
    let o = one Order in orders where o.total == 25
  }
  when {
    commerce.pay(o)
  }
  then {
    assert o.status == @Paid
  }
}
```

## Programs and procs

```abide
proc release(editorial: Editorial) {
  submit = editorial.submit_pending()
  approve = editorial.approve_pending()
  publish = editorial.publish_pending()

  approve needs submit
  publish needs approve
}

program Publishing(documents: Store<Document>[..4]) {
  let editorial = Editorial { documents: documents }
  use release(editorial)
}
```

## Temporal operators

```abide
always p
eventually p
p until q
historically p
once p
previously p
p since q
saw Commerce::pay(_)
```

## Quantifiers and aggregates

```abide
all o: Order | o.total >= 0
exists o: Order | o.total > 0
some o: Order | o.total > 0
no o: Order | o.status == @Cancelled
lone o: Order | o.status == @Draft

count o: Order in orders | o.total > 0
sum o: Order in orders | o.total
max o: Order in orders | o.total
```

## Imperative functions

```abide
fn gcd(a: int, b: int): int
  requires a > 0
  requires b >= 0
  ensures result > 0
  decreases b
{
  var x = a
  var y = b
  while y != 0
    invariant x > 0
    decreases y
  {
    var tmp = y
    y = x % y
    x = tmp
  }
  x
}
```

## Structural patterns

- Systems are declared over explicit `Store<T>` pools.
- Public operations are described with `command` and `query`.
- Orchestration is described with `proc` and `program`.
