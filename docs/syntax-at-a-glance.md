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
system Commerce(orders: Store<Order>) {
  command pay(order_id: identity) {
    choose order: Order where order.id == order_id and order.status == @Pending {
      order.mark_paid()
    }
  }

  query payable(order: Order) =
    order.status == @Pending and order.total > 0

  pred non_negative(order: Order) =
    order.total >= 0
}
```

Notes:
- `Store<T>` constructor params are the current entity-pool surface.
- Store constructor params may optionally carry cardinality contracts: `Store<Order>[N]`, `Store<Order>[lo..hi]`, or `Store<Order>[..hi]`.
- Concrete checking scopes belong in `store` declarations inside `assume` or `given` blocks. The lower bound is the active floor and the upper bound is store capacity. Explicit `activate {o1} in orders` clauses bind named instances to initial slots; anonymous slots satisfy any remaining nonzero floor. Create actions may grow the active population up to the upper bound.
- `command` declares the public API and may carry its executable body inline.
- `query` is public and pure.
- `action` is private implementation behavior called by commands or other internal behavior.
- `pred` is internal and pure.

## Predicate-shaped choices

| Need | Construct |
| --- | --- |
| Public read-only observation | `query` |
| Private Boolean helper | `pred` |
| Reusable pure computation | `fn` |
| Computed entity/system field | `derived` |
| Durable entity/system state fact | `invariant` |
| Auto-verified system property | `prop` |
| Reusable proof fact | `lemma` |
| Proof-style obligation | `theorem` |

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

`by "..."` is a trusted proof-artifact reference. Abide records and reports the
locator and inferred backend, but it does not check the external proof file in
the current verifier pipeline; results disclose these as unchecked trusted
references.

## Extern Dependencies

```abide
extern Stripe {
  command charge(order_id: int) -> Outcome
  may charge { return @ok }
}

system Billing(orders: Store<Order>) {
  dep Stripe

  command submit(order_id: identity) {
    Stripe::charge(order_id)
  }
}
```

`dep` declarations are validation-only metadata. They authorize calls from a
system to a declared `extern`, but they do not import names, instantiate runtime
objects, or add verifier assumptions by themselves. Extern behavior comes from
the extern block's `may` clauses and from actual calls that appear in commands.

## Interfaces and Extern Boundaries

```abide
interface PaymentProcessor {
  command authorize(order_id: identity, amount: int) -> string
}

extern StripeGateway implements PaymentProcessor {
  command authorize(order_id: identity, amount: int) -> string

  may authorize {
    return "approved"
    return "declined"
  }
}

system Checkout(orders: Store<Order>) {
  dep StripeGateway

  command checkout(order_id: identity) {
    choose o: Order where o.id == order_id {
      StripeGateway::authorize(o.id, o.total)
    }
  }
}
```

Interfaces are contract metadata over concrete systems and externs. They do not
create runtime stores, schedule events, or introduce a verifier target by
themselves. A `system ... implements Interface` or
`extern ... implements Interface` declaration must provide the command and query
surface declared by the interface; a missing command or query is a conformance
error, and command return types must match.

Use the concrete system or extern name when behavior matters. System commands
call extern commands through an explicit `dep`, and temporal observations use
the concrete boundary event, for example `saw StripeGateway::authorize(_, _)`.
Tooling also exposes interface metadata: `ask interfaces` in QA lists interface
declarations and their system or extern implementors, and editor completions can
offer declared interface names.

## Scenes

```abide
scene successful_payment {
  given {
    store orders: Order[1]
    activate {o} in orders
    let commerce = Commerce { orders: orders }
    o.total == 25
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
