# Core Concepts

Abide models stateful systems, their public command surfaces, and the properties they must satisfy.

## Entities

Entities are stateful domain objects with identity, fields, and actions.

```abide
entity Account {
  id: identity
  balance: real = 0

  action deposit(amount: real)
    requires amount > 0 {
    balance' = balance + amount
  }
}
```

- Fields describe persistent state.
- `action` bodies describe guarded transitions.
- Primed fields such as `balance'` refer to post-state values.

## Systems

Systems operate over explicit entity pools:

```abide
system Banking(accounts: Store<Account>) {
  command deposit(account: Account, amount: real)
    requires amount > 0 {
    account.deposit(amount)
  }
}
```

Key points:
- `Store<T>` constructor parameters define the entity pools the system can operate over.
- Store parameter bounds are optional cardinality contracts: `[N]` for exact size, `[lo..hi]` for a range, and `[..hi]` for at most `hi`.
- Concrete checking scopes belong in `store` declarations inside `assume` or `given` blocks. Those bounds define the active startup population and maximum create capacity for that check or scene.
- `command` declares public operations and may include executable bodies inline.
- `query` exposes pure read-only observations.
- `pred` stays internal to the system.

## Verification blocks

`verify` checks universal properties:

```abide
verify no_negative_balances {
  assume {
    store accounts: Account[0..8]
    let banking = Banking { accounts: accounts }
  }
  assert always all a: Account | a.balance >= 0
}
```

The `assume` block establishes:
- finite store bounds
- instantiated systems
- fairness, stutter, and related execution assumptions when needed

## Theorems and lemmas

`theorem` and `lemma` express unbounded proof obligations and reusable facts:

```abide
theorem shipped_orders_have_value =
  always all o: Order | o.status == @Shipped implies o.total > 0

lemma positive_amounts {
  all o: Order | o.total >= 0
}
```

## Scenes

`scene` checks existential witnesses:

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

Use scenes when you want to show that some behavior is possible, not that it is universally required.

## Temporal logic

Abide’s temporal surface includes:
- `always`
- `eventually`
- `until`
- past-time operators such as `historically`, `once`, `previously`, `since`
- `saw` for observation-style command reasoning

Fairness is declared at the verification site, not on commands:

```abide
verify fair_toggle {
  assume {
    store signals: Signal[0..3]
    let traffic = Traffic { signals: signals }
    fair Traffic::toggle
    strong fair Traffic::reset
  }
  assert all s: Signal | s.color == @Red implies eventually s.color == @Green
}
```

## Relations

Relations model finite links between values. `Rel<T...>` is the
first-class collection type for finite tuple relations:

```abide
enum OrderStage = Draft | Paid | Shipped
enum FulfillmentPhase = Open | Complete
enum HandlingLane = Manual | Automated

type StagePhaseRel = Rel<OrderStage, FulfillmentPhase>
type StagePhaseLaneRel = Rel<(OrderStage, FulfillmentPhase, HandlingLane)>

verify stage_lane_links {
  assert Rel((@Draft, @Open), (@Paid, @Open), (@Shipped, @Complete))
    |> Rel::join(Rel((@Open, @Manual), (@Complete, @Automated)))
    == Rel((@Draft, @Manual), (@Paid, @Manual), (@Shipped, @Automated))
}
```

`Rel<A, B>` is a binary relation. `Rel<(A, B, C)>` is an explicit
n-ary relation. Relation literals use `Rel(...)`; each element is either a
single value for a unary relation or a tuple for a multi-column relation.

Supported relation operations:

- `Rel::join(left, right)` composes two relations by matching the last column of `left` with the first column of `right`. Joining `Rel<(OrderStage, FulfillmentPhase)>` with `Rel<(FulfillmentPhase, HandlingLane)>` yields `Rel<(OrderStage, HandlingLane)>`.
- `Rel::transpose(relation)` reverses the columns of a binary relation. `Rel<(OrderStage, FulfillmentPhase)>` becomes `Rel<(FulfillmentPhase, OrderStage)>`.
- `Rel::closure(relation)` computes the transitive closure of a homogeneous binary relation. It includes paths of one or more edges.
- `Rel::reach(relation)` computes the reflexive transitive closure of a homogeneous binary relation. It includes the same paths as `closure`, plus identity pairs for every value in the relation's finite domain.
- `Rel::product(left, right)` computes the cartesian product of two relations. Product appends the columns of `right` after the columns of `left`.
- `Rel::project(relation, column)` keeps one column from a relation. Columns are zero-based.
- `Rel::field(store, Entity::field)` derives the current store-backed relation from active entities to one of their finite fields.

Pipeline form is supported when the relation operation remains fully qualified:

```abide
Rel((@Draft, @Open), (@Paid, @Open))
  |> Rel::join(Rel((@Open, @Manual)))
```

Examples:

```abide
verify relation_examples {
  assert Rel::transpose(Rel((@Draft, @Open)))
    == Rel((@Open, @Draft))

  assert Rel::closure(Rel((@Draft, @Paid), (@Paid, @Shipped)))
    == Rel((@Draft, @Paid), (@Paid, @Shipped), (@Draft, @Shipped))

  assert #Rel::product(Rel(@Draft, @Paid), Rel(@Manual)) == 2

  assert Rel::project(Rel((@Draft, @Open, @Manual)), 0)
    == Rel(@Draft)
}
```

`Rel::field(orders, Order::status)` derives the finite relation of active store
members to their field values:

```abide
assert always Rel::field(orders, Order::status)
  <= Rel::field(orders', Order::status)
```

Relation comprehensions build finite relations from active store members:

```abide
assert always Rel((o, c) | o: Order in orders, c: Customer in customers where o.customer_id == c.id)
  <= (Rel::field(orders, Order::customer_id) |> Rel::join(Rel::transpose(Rel::field(customers, Customer::id))))
```

The same relation operations compose over store-backed comprehensions. For
example, `Rel::reach(Rel((a, b) | a: Node in nodes, b: Node in nodes where a.next_id == b.id))`
checks finite reachability through the active node store.

Static relation verification supports equality, subset, and cardinality over
finite relation expressions. Counterexamples render the computed tuples so
the mismatch can be inspected directly.

## Collection comprehensions

Set comprehensions filter finite domains and can project each selected value:

```abide
{ o: Order where o.status == @Paid }
{ o.total | o: Order where o.status == @Paid }
```

When the source is an explicit finite collection, use `in source`. The binder
type may be written or inferred from `Set<T>` and `Seq<T>` sources:

```abide
{ x * 2 | x: int in Set(1, 2, 3) where x > 1 }
{ amount | amount in Seq(10.0, 25.0, 50.0) where amount >= 25.0 }
```

## Programs and procs

For command orchestration, Abide provides `proc` and `program`:

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

## Terminology

- `command` is the public system operation surface.
- `action` is private executable behavior inside an entity or system.
- `program` and `proc` describe orchestration structure.
