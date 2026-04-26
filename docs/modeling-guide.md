# Modeling Guide

This guide is about how to structure Abide models with the syntax and verification model the compiler accepts today.

## Start with types and entities

Types define vocabulary. Entities define persistent state and transitions.

```abide
enum OrderStatus = Pending | Confirmed | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real = 0

  action confirm()
    requires status == @Pending
    requires total > 0 {
    status' = @Confirmed
  }
}
```

Use:
- `enum` for finite state vocabularies
- `struct` for plain product data
- `type` for aliases and refinements
- `entity` for stateful things with identity

## Systems are store-backed boundaries

Current Abide systems take explicit store pools:

```abide
system Commerce(orders: Store<Order>) {
  command confirm_order(order_id: identity)

  step confirm_order(order_id: identity) {
    choose o: Order where o.id == order_id {
      o.confirm()
    }
  }
}
```

Model systems over explicit `Store<T>` pools and route behavior through commands and steps.

## Commands, steps, queries, predicates

Use the system surface deliberately:

- `command` — public callable operation
- `step` — executable clause implementing a command
- `query` — public pure observation
- `pred` — internal pure helper

```abide
system Billing(orders: Store<Order>) {
  command charge(order: Order)

  query payable(order: Order) =
    order.status == @Pending and order.total > 0

  step charge(order: Order)
    requires payable(order) {
    order.mark_paid()
  }
}
```

## Use identity params when selection matters

For public APIs, identity-based command params are usually clearer than exposing unrestricted entity picks:

```abide
command ship_order(order_id: identity)

step ship_order(order_id: identity) {
  choose o: Order where o.id == order_id {
    o.ship()
  }
}
```

This makes witness traces and cross-system routing easier to read.

## Verification uses explicit assumptions

Current verify blocks do not use `for System[0..N]`. They use an `assume` block with stores and instantiated systems:

```abide
verify shipped_orders_have_value {
  assume {
    store orders: Order[0..6]
    let commerce = Commerce { orders: orders }
  }
  assert always all o: Order | o.status == @Shipped implies o.total > 0
}
```

That assumption block is also where fairness and stutter settings live:

```abide
verify fair_progress {
  assume {
    store orders: Order[0..6]
    let commerce = Commerce { orders: orders }
    fair Commerce::confirm_order
    strong fair Commerce::ship_order
  }
  assert all o: Order | o.status == @Confirmed implies eventually o.status == @Shipped
}
```

## Scenes are existential witnesses

Use scenes to demonstrate reachability or successful workflows:

```abide
scene paid_order_can_ship {
  given {
    store orders: Order[1..1]
    let commerce = Commerce { orders: orders }
    let o = one Order in orders where o.status == @Confirmed
  }
  when {
    commerce.ship_order(o.id)
  }
  then {
    assert o.status == @Shipped
  }
}
```

## Workflow orchestration

```abide
proc release(editorial: Editorial) {
  submit = editorial.submit_pending()
  approve = editorial.approve_pending()
  publish = editorial.publish_pending()

  approve needs submit.ok
  publish needs approve.ok
}

program Publishing(documents: Store<Document>) {
  let editorial = Editorial { documents: documents }
  use release(editorial)
}
```

Use `proc` when you want dependency-structured command execution, branching on outcomes, or reusable orchestration logic.

## Cross-system coordination

System steps can call other systems directly:

```abide
step process_payment(intent_id: identity) {
  choose p: PaymentIntent where p.id == intent_id {
    p.capture()
    Commerce::confirm_payment(p.order_id)
  }
}
```

This is the right place to model service-to-service orchestration.

## Functions are for local computation

Keep business computations in `fn` declarations with contracts:

```abide
fn clamp(x: int, lo: int, hi: int): int
  requires lo <= hi
  ensures result >= lo
  ensures result <= hi
{
  if x < lo { lo } else { if x > hi { hi } else { x } }
}
```

Use imperative function bodies when they make the logic clearer:

```abide
fn sum_to(n: int): int
  requires n >= 0
{
  var total = 0
  var i = 0
  while i <= n
    invariant total >= 0
    decreases n - i
  {
    total = total + i
    i = i + 1
  }
  total
}
```

## Recommended modeling order

1. Define enums, structs, and refinement aliases.
2. Define entities and actions.
3. Define systems over explicit `Store<T>` pools.
4. Add `command`, `step`, `query`, and `pred`.
5. Add `verify` and `scene` blocks.
6. Add `proc` / `program` only when orchestration structure matters.

This keeps the model readable and makes verification failures easier to diagnose.
