# Examples

Curated examples live in [`abide-lang/examples/`](../examples/). Examples with
top-level `verify` blocks are intended to run with the bounded verifier, either
as a whole file or by selecting a specific target:

```bash
abide verify examples/<name>.ab
abide verify examples/<name>.ab --target verify:<target>
```

Ordinary `verify` defaults to bounded/exploration checking. Add `--ic3` or
`--unbounded-only` only when you intentionally want proof-search behavior.

Some syntax-focused examples contain only functions, predicates, scenes, or data
model declarations. Use `--no-fn-verify` or `--no-prop-verify` for quick parser
and elaboration smoke checks when you do not want implicit proof obligations.

Intentional failure examples are listed separately at the end. Run them by
target name because the expected outcome is a verifier failure.

Expected bounded verify targets:

| Example | Target | Expected bounded verdict |
| --- | --- | --- |
| `advanced_temporal.ab` | `until_and_history` | `CHECKED` |
| `banking.ab` | `account_safety` | `CHECKED` |
| `collections.ab` | `set_source_comprehension` | `CHECKED` |
| `collections.ab` | `typed_set_source_comprehension` | `CHECKED` |
| `collections.ab` | `seq_source_comprehension` | `CHECKED` |
| `commerce.ab` | `payment_integrity` | `CHECKED` |
| `healthcare.ab` | `admitted_patients_have_rooms` | `CHECKED` |
| `order.ab` | `shipped_orders_have_positive_totals` | `CHECKED` |
| `orchestration.ab` | `published_documents_leave_draft` | `PROVED` |
| `proofs_and_boundaries.ab` | `closed_tickets_stay_closed` | `CHECKED` |
| `proofs_and_boundaries.ab` | `open_tickets_eventually_close` | `CHECKED` |
| `relations.ab` | `stage_lane_join` | `CHECKED` |
| `relations.ab` | `transpose_flips_columns` | `CHECKED` |
| `relations.ab` | `lifecycle_reachability` | `CHECKED` |
| `relations.ab` | `lifecycle_reachability_with_identity` | `CHECKED` |
| `relations.ab` | `product_cardinality` | `CHECKED` |
| `relations.ab` | `projection_keeps_order_ids` | `CHECKED` |
| `relations.ab` | `filtered_relation_comprehension_matches_join` | `CHECKED` |
| `relations.ab` | `store_backed_relation_reachability` | `CHECKED` |
| `state_modeling.ab` | `state_modeling_smoke` | `CHECKED` |

## Minimal order lifecycle

See: [`examples/order.ab`](../examples/order.ab)

Highlights:
- store-backed system constructor: `system Orders(orders: Store<Order>)`
- public identity-based `command` bodies
- public read-only `query`
- private entity `action` calls inside commands
- `verify` with `assume { store ...; let ... }`

```abide
system Orders(orders: Store<Order>) {
  query payable(order: Order) =
    order.status == @Pending and order.total > 0

  command confirm_order(order_id: identity) {
    choose order: Order where order.id == order_id and order.status == @Pending and order.total > 0 {
      order.confirm()
    }
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

## Advanced: proofs and external boundaries

See: [`examples/proofs_and_boundaries.ab`](../examples/proofs_and_boundaries.ab)

Highlights:
- refinement type aliases and contract checking
- lemma, axiom, and theorem result reporting
- `by "..."` proof-artifact references as unchecked trusted references
- liveness/fairness in bounded verification
- extern `dep` declarations and disclosed extern assumptions

## Interface and extern contract boundaries

See: [`examples/external_payment_provider.ab`](../examples/external_payment_provider.ab)

Highlights:
- `interface` declarations as contract metadata over concrete systems and externs
- `extern StripeGateway implements PaymentProcessor`
- extern `may` blocks describing allowed command results
- concrete extern calls authorized by `dep`
- `saw StripeGateway::authorize(...)` in a scene to observe the boundary call
- `ask interfaces` in QA to list interface declarations and implementors

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
```

An interface does not run by itself. It records the command/query contract that
concrete systems or externs claim to implement. If an implementor omits a
required command/query, the missing command or query is a conformance error
during checking; a command with a different return type is also rejected.
Verification and scenes still name the concrete system or extern boundary.

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
