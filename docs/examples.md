# Examples

Curated examples live in [`abide-lang/examples/`](../examples/). Every example listed here parses on current `master`.

## Minimal order lifecycle

See: [`examples/order.ab`](../examples/order.ab)

Highlights:
- store-backed system constructor: `system Orders(orders: Store<Order>[..4])`
- inline `command` bodies
- `query`
- `verify` with `assume { store ...; let ... }`

```abide
system Orders(orders: Store<Order>[..4]) {
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
system Banking(accounts: Store<Account>[..8]) {
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
system Billing(orders: Store<Order>[..6], intents: Store<PaymentIntent>[..6]) {
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

## Workflow orchestration

See: [`examples/workflow.ab`](../examples/workflow.ab)

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

## Functions and imperative verification

See:
- [`examples/algorithms.ab`](../examples/algorithms.ab)
- [`examples/contracts.ab`](../examples/contracts.ab)
- [`examples/imperative.ab`](../examples/imperative.ab)

Highlights:
- `requires`, `ensures`, `decreases`
- recursion and termination
- imperative `var` / `while` / invariants

## Pattern matching

See: [`examples/matching.ab`](../examples/matching.ab)

Highlights:
- ADTs with payloads
- guarded match arms
- wildcard and rest patterns
