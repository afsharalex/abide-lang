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
- Store bounds also define the active startup population: `[N]` starts with exactly `N` active entities, `[lo..hi]` starts with `lo`, and `[..hi]` starts with `0`; create actions may grow the active population up to the upper bound.
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

## Collections

Set comprehensions can filter a typed domain:

```abide
{ o: Order where o.status == @Paid }
```

They can also project/map each selected value:

```abide
{ o.total | o: Order where o.status == @Paid }
```

For finite collection sources, add `in source`. The binder type can be written
explicitly or inferred from the source collection:

```abide
{ x * 2 | x: int in Set(1, 2, 3) where x > 1 }
{ amount | amount in Seq(10.0, 25.0, 50.0) where amount >= 25.0 }
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

## Relations

Relations are finite sets of tuples. Unary relations are ordinary sets, and
binary or wider relations use tuple elements:

```abide
enum OrderStage = Draft | Paid | Shipped
enum FulfillmentPhase = Open | Complete
enum HandlingLane = Manual | Automated

type StagePhaseRel = Rel<OrderStage, FulfillmentPhase>
type StagePhaseLaneRel = Rel<(OrderStage, FulfillmentPhase, HandlingLane)>

Rel(@Draft, @Paid)
Rel((@Draft, @Open), (@Shipped, @Complete))
```

Relation operations are associated operations on the first-class `Rel` type:

```abide
Rel::join(
  Rel((@Draft, @Open), (@Paid, @Open), (@Shipped, @Complete)),
  Rel((@Open, @Manual), (@Complete, @Automated))
)

Rel::transpose(Rel((@Draft, @Open)))
Rel::closure(Rel((@Draft, @Paid), (@Paid, @Shipped)))
Rel::reach(Rel((@Draft, @Paid), (@Paid, @Shipped)))
Rel::product(Rel(@Draft, @Paid), Rel(@Manual))
Rel::project(Rel((@Draft, @Open, @Manual)), 0)
Rel::field(orders, Order::status)

Rel((@Draft, @Open), (@Paid, @Open))
  |> Rel::join(Rel((@Open, @Manual)))
```

Store-backed comprehensions can be passed to the same operations:

```abide
Rel::reach(Rel((a, b) | a: Node in nodes, b: Node in nodes where a.next_id == b.id))
```

Static relation checks support equality, subset, and cardinality:

```abide
verify stage_lane_join {
  assert Rel((@Draft, @Open), (@Paid, @Open), (@Shipped, @Complete))
    |> Rel::join(Rel((@Open, @Manual), (@Complete, @Automated)))
    == Rel((@Draft, @Manual), (@Paid, @Manual), (@Shipped, @Automated))
}

verify product_size {
  assert #Rel::product(Rel(@Draft, @Paid), Rel(@Manual)) == 2
}

verify lifecycle_reachability {
  assert Rel::reach(Rel((@Draft, @Paid), (@Paid, @Shipped))) == Rel(
    (@Draft, @Draft),
    (@Paid, @Paid),
    (@Shipped, @Shipped),
    (@Draft, @Paid),
    (@Paid, @Shipped),
    (@Draft, @Shipped)
  )
}
```

Relation comprehensions over finite stores use a tuple projection, one or more
typed store bindings, and a `where` filter:

```abide
Rel((o, c) | o: Order in orders, c: Customer in customers where o.customer_id == c.id)
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
