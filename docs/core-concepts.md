# Core Concepts

Abide models stateful systems, their public command surfaces, and the properties they must satisfy.

## Modeling ladder

The usual path is:

1. Define durable state with `entity`.
2. Put public behavior behind a `system`.
3. Expose mutation with `command`.
4. Expose read-only observations with `query`.
5. Keep `action` as private implementation behavior called by commands.
6. Use `verify` for universal checks.
7. Use `scene` for concrete examples and witnesses.
8. Reach for `theorem` and `lemma` only when you need proof-style obligations.
9. Use QA, the REPL, `run`, and `explore` to inspect a model while you refine it.

## Entities

Entities are stateful domain objects with identity, fields, and private actions.

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
- `action` bodies describe guarded implementation transitions.
- Primed fields such as `balance'` refer to post-state values.

## Systems

Systems operate over explicit entity pools:

```abide
system Banking(accounts: Store<Account>) {
  command deposit(account_id: identity, amount: real)
    requires amount > 0 {
    choose account: Account where account.id == account_id {
      account.deposit(amount)
    }
  }
}
```

Key points:
- `Store<T>` constructor parameters define the entity pools the system can operate over.
- Store parameter bounds are optional cardinality contracts: `[N]` for exact size, `[lo..hi]` for a range, and `[..hi]` for at most `hi`.
- Concrete checking scopes belong in `store` declarations inside `assume` or `given` blocks. Those bounds define capacity for that check or scene; stores start empty unless the block explicitly activates named entities.
- `command` declares public operations and may include executable bodies inline.
- `query` exposes pure read-only observations.
- Public application-shaped commands usually take identity or value parameters and choose the target entity inside the command. Entity-valued parameters are still useful for concise specs and closed-world examples.
- Entity and system `action` declarations are private implementation behavior, not the public API.
- `pred` stays internal to the system.

## Predicate-shaped constructs

When several constructs could name a Boolean or fact, choose by audience:

- Public read-only observation: use `query`.
- Private Boolean helper: use `pred`.
- Reusable pure computation: use `fn`, even when it returns `bool`.
- Computed entity/system field: use `derived`.
- Durable entity/system state fact: use `invariant`.
- Named system property that should be auto-verified: use `prop`.
- Reusable proof fact: use `lemma`.
- Proof-style obligation: use `theorem`.

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
- explicitly activated initial entities, when a scenario needs pre-existing objects
- bare Boolean predicates over stores that must hold in the initial state
- fairness, stutter, and related execution assumptions when needed

A `CHECKED` result means Abide did not find a counterexample on the explored
bounded trace prefixes. The reported depth is a transition bound and may include
stutter steps when stutter is enabled. It is not a TLC-style exhaustive
reachable-state result and not an Alloy-style all-instance result. Ordinary
`verify` uses this bounded/exploration workflow by default; when you want an
unbounded proof attempt for a verify block, rerun with an explicit proof-search
flag such as `--ic3` or use `theorem` for proof-oriented claims.

Choose verification and inspection constructs by the question you are asking:

- Could this fail? Use `verify`.
- Can this happen? Use `scene`.
- Should this reusable system property be checked automatically? Use `prop`.
- Does this need an unbounded proof-style obligation? Use `theorem`.
- Is this a reusable proof fact? Use `lemma`.
- Is this an external trust boundary? Use `axiom`.
- Is this a structural or CI question? Use QA `ask`, `explain`, or `assert`.
- Do you want one concrete execution? Use `simulate` or `run`.
- Do you want a bounded state-space artifact? Use `explore`.

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

Use scenes when you want to show that some behavior is possible, not that it is universally required.
Events listed in a `when` block run in textual order by default. To ask for a different shape, bind event calls with `let` and add an explicit `assume` using composition operators such as `->` for sequence, `&` for same-step, `||` for concurrent, or `|`/`^|` for choice.
Use `implies` for logical implication in assertions and properties; `->` is reserved for sequence composition and function types.

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
- `query` is the public read-only system observation surface.
- `action` is private executable behavior inside an entity or system.
- `program` and `proc` describe orchestration structure.
