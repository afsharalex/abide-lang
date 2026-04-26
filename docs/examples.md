# Examples

Curated examples demonstrating Abide's features. Each builds on the previous. All examples parse with the current compiler.

Complete files are in the `examples/` directory.

---

## Minimal: Order Entity

The simplest useful spec — an entity with a status enum and two actions.

```abide
enum OrderStatus = Pending | Paid | Shipped

entity Order {
  id: identity
  status: OrderStatus = @Pending
  total: real

  action pay() requires status == @Pending requires total > 0 {
    status' = @Paid
  }

  action ship() requires status == @Paid {
    status' = @Shipped
  }
}
```

Key concepts: enums define state vocabulary, entities hold state, actions transition state with guards, `'` notation distinguishes current from next state.

See: [`examples/order.ab`](../examples/order.ab)

---

## Banking: Rich Entity with Verification

An account with multiple actions, predicates, constants, and verification.

```abide
const MAX_WITHDRAWAL = 10000

entity Account {
  id: identity
  balance: real
  status: AccountStatus = @Active

  action deposit(amount: real)
    requires status == @Active
    requires amount > 0
    ensures balance' == balance + amount {
    balance' = balance + amount
  }

  action withdraw(amount: real)
    requires status == @Active
    requires amount > 0
    requires amount <= MAX_WITHDRAWAL
    requires balance >= amount
    ensures balance' == balance - amount {
    balance' = balance - amount
  }

  action freeze() requires status == @Active {
    status' = @Frozen
  }
}

pred is_active(a: Account) = a.status == @Active
pred has_funds(a: Account, amount: real) = a.balance >= amount

verify account_safety for Banking[0..500] {
  assert always (all a: Account | a.balance >= 0)
  assert always (all a: Account |
    a.status == @Frozen implies a.balance' == a.balance)
}

scene successful_deposit for Banking {
  given let a = one Account where a.status == @Active and a.balance == 1000
  when action dep = Banking::deposit(a, 500) { one }
  then assert a.balance == 1500
}
```

Key concepts: `requires`/`ensures` contracts, constants, predicates as named constraints, `verify` with bounded checking, `scene` with given/when/then.

See: [`examples/banking.ab`](../examples/banking.ab)

---

## Workflow: State Machine with Roles

A document review lifecycle with role-based guards and temporal properties.

```abide
enum DocStatus = Draft | Submitted | UnderReview | Approved | Rejected | Published

entity Document {
  id: identity
  status: DocStatus = @Draft
  author_id: identity
  reviewer_id: identity
  revision_count: int = 0

  action submit() requires status == @Draft {
    status' = @Submitted
  }

  action begin_review(reviewer: identity)
    requires status == @Submitted
    requires reviewer != author_id {
    status' = @UnderReview
    reviewer_id' = reviewer
  }

  action approve() requires status == @UnderReview {
    status' = @Approved
  }

  action reject() requires status == @UnderReview {
    status' = @Rejected
  }

  action revise() requires status == @Rejected {
    status' = @Draft
    revision_count' = revision_count + 1
  }

  action publish() requires status == @Approved {
    status' = @Published
  }
}

prop reviewer_not_author = all d: Document |
  d.status == @UnderReview implies d.reviewer_id != d.author_id

verify review_integrity for Publishing[0..200] {
  assert always (all d: Document |
    d.status == @UnderReview implies d.reviewer_id != d.author_id)
  assert all d: Document |
    d.status == @Submitted implies
      eventually (d.status == @Approved or d.status == @Rejected)
}
```

Key concepts: multi-step state machines, role separation (`reviewer != author_id`), revision counting, liveness properties.

See: [`examples/workflow.ab`](../examples/workflow.ab)

---

## Pattern Matching

Sum types with record variants and comprehensive match expressions.

```abide
enum Shape =
  Circle { radius: real }
  | Rectangle { width: real, height: real }
  | Triangle { base: real, height: real }
  | Point

fn area(s: Shape): real =
  match s {
    Circle { radius: r } => 3.14159 * r * r
    Rectangle { width: w, height: h } => w * h
    Triangle { base: b, height: h } => 0.5 * b * h
    Point => 0
  }

fn describe(s: Shape): string =
  match s {
    Circle { radius: r } if r > 100 => "large circle"
    Circle { .. } => "circle"
    Rectangle { width: w, height: h } if w == h => "square"
    Rectangle { .. } => "rectangle"
    _ => "other shape"
  }
```

Key concepts: ADT variants with record fields, destructuring, guards (`if`), rest patterns (`..`), wildcards (`_`).

See: [`examples/matching.ab`](../examples/matching.ab)

---

## Multi-System: Commerce with Billing

Two systems coordinating through cross-system event calls.

```abide
system Commerce {
  use Order

  event submit_order(o: Order) requires o.status == @Pending {
    o.submit()
  }

  event confirm_payment(o: Order) requires o.status == @AwaitingPayment {
    o.mark_paid()
  }
}

system Billing {
  use Order

  event process_payment(o: Order)
    requires o.status == @AwaitingPayment {
    Commerce::confirm_payment(o)
  }
}

verify cross_system_payment for Commerce[0..100], Billing[0..100] {
  assert all o: Order |
    o.status == @Paid implies o.total > 0
}
```

Key concepts: multiple systems sharing entities, cross-system event calls (`Commerce::confirm_payment`), multi-system verification bounds.

See: [`examples/commerce.ab`](../examples/commerce.ab)

---

## Healthcare: Rich Domain with Proofs

A condensed healthcare specification showing entities, ADTs, predicates, and proof blocks.

```abide
enum DosageForm =
  Tablet { mg: int }
  | Liquid { ml: int }
  | Injection { dose_mg: int }

entity Prescription {
  id: identity
  patient_id: identity
  status: PrescriptionStatus = @Prescribed
  dosage: DosageForm
  refills_remaining: int = 0

  action dispense() requires status == @Prescribed {
    status' = @Dispensed
  }

  action refill()
    requires status == @Dispensed
    requires refills_remaining > 0 {
    refills_remaining' = refills_remaining - 1
  }
}

fn daily_dose(d: DosageForm): int =
  match d {
    Tablet { mg: m } => m
    Liquid { ml: m } => m * 5
    Injection { dose_mg: d } => d
  }

lemma refill_decreases {
  all rx: Prescription |
    rx.status == @Dispensed and rx.refills_remaining > 0 implies
      rx.refills_remaining' == rx.refills_remaining - 1
}
```

Key concepts: ADTs with record variants in entity fields, match in functions, refill mechanics with arithmetic, lemma for refill property.

See: [`examples/healthcare.ab`](../examples/healthcare.ab)

---

## More Examples

The `examples/` directory contains complete, self-contained specification files. Each file can be parsed independently with `abide parse <file>`.
