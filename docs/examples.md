# Examples

Curated examples live in [`abide-lang/examples/`](../examples/). Every example listed here is intended to run under:

```bash
abide verify examples/<name>.ab --bounded-only
```

Intentional failure examples are listed separately at the end. Run them by
target name because the expected outcome is a verifier failure.

## Minimal order lifecycle

See: [`examples/order.ab`](../examples/order.ab)

Highlights:
- store-backed system constructor: `system Orders(orders: Store<Order>)`
- inline `command` bodies
- `query`
- `verify` with `assume { store ...; let ... }`

```abide
system Orders(orders: Store<Order>) {
  query payable(order: Order) =
    order.status == @Pending and order.total > 0

  command confirm_order(order: Order)
    requires payable(order) {
    order.confirm()
  }
}
```

## Banking

See: [`examples/banking.ab`](../examples/banking.ab)

Highlights:
- entity actions with guards
- `create` and `choose`
- store-bounded verification
- existential witness scenes

```abide
system Banking(accounts: Store<Account>) {
  command deposit(account_id: identity, amount: real)
    requires amount > 0 {
    choose a: Account where a.id == account_id {
      a.deposit(amount)
    }
  }
}
```

## Commerce and billing

See: [`examples/commerce.ab`](../examples/commerce.ab)

Highlights:
- multiple systems sharing stores
- cross-system command calls
- public `query` surface

```abide
system Billing(orders: Store<Order>, intents: Store<PaymentIntent>) {
  command process_payment(intent_id: identity) {
    choose p: PaymentIntent where p.id == intent_id {
      p.capture()
      Commerce::confirm_payment(p.order_id)
    }
  }
}
```

## Healthcare

See: [`examples/healthcare.ab`](../examples/healthcare.ab)

Highlights:
- multiple entity types
- multiple systems over shared stores
- predicates reused in command guards

## Command orchestration

See: [`examples/orchestration.ab`](../examples/orchestration.ab)

Highlights:
- `proc` dependency graphs
- `program` composition roots
- `needs` edges

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

## Collection comprehensions

See: [`examples/collections.ab`](../examples/collections.ab)

Highlights:
- set comprehensions over finite `Set(...)` sources
- set comprehensions over finite `Seq(...)` sources
- binder type inference from source collections
- explicit binder type annotations when desired

```abide
assert { x * 2 | x in Set(1, 2, 3) where x > 1 } == Set(4, 6)

assert { amount | amount in Seq(10.0, 25.0, 50.0) where amount >= 25.0 }
  == Set(25.0, 50.0)
```

## Functions and imperative verification

See:
- [`examples/algorithms.ab`](../examples/algorithms.ab)
- [`examples/contracts.ab`](../examples/contracts.ab)
- [`examples/imperative.ab`](../examples/imperative.ab)

Highlights:
- `requires`, `ensures`, `decreases`
- recursion and termination
- imperative `var` / `while` / invariants

## Proofs and external boundaries

See: [`examples/proofs_and_boundaries.ab`](../examples/proofs_and_boundaries.ab)

Highlights:
- refinement type aliases and contract checking
- lemma, axiom, and theorem result reporting
- `by "..."` proof-artifact references as unchecked trusted references
- liveness/fairness in bounded verification
- extern `dep` declarations and disclosed extern assumptions

## Advanced temporal operators

See: [`examples/advanced_temporal.ab`](../examples/advanced_temporal.ab)

Highlights:
- `under { ... }` shared assumptions
- `until`, `historically`, and `since`
- extern-boundary `saw`
- scene checking with observed extern calls

## State modeling surface

See: [`examples/state_modeling.ab`](../examples/state_modeling.ab)

Highlights:
- `interface` conformance
- entity and system `invariant` declarations
- `fsm` transition tables
- `derived` fields

## Pattern matching

See: [`examples/matching.ab`](../examples/matching.ab)

Highlights:
- ADTs with payloads
- guarded match arms
- wildcard and rest patterns

## Intentional failures

See:
- [`examples/intentional_failures.ab`](../examples/intentional_failures.ab)
- [`examples/intentional_timeout.ab`](../examples/intentional_timeout.ab)

Expected failure commands:

```bash
abide verify examples/intentional_failures.ab --target verify:violated_claim --bounded-only
abide verify examples/intentional_failures.ab --target verify:violated_invariant --bounded-only
abide verify examples/intentional_failures.ab --target verify:deadlocked_without_stutter --bounded-only
abide verify examples/intentional_timeout.ab --target verify:large_scope_search --bounded-only --timeout 1
```

The first two commands demonstrate counterexamples, the third demonstrates
deadlock reporting under explicit `no stutter`, and the timeout example is a
budget-stress demo whose exact outcome depends on local solver speed.
