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
    store orders: Order[1..1]
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
- `saw` for observation-style event reasoning

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

## Programs and procs

For workflow-style orchestration, Abide provides `proc` and `program`:

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

## Terminology

- `command` is the public system operation surface.
- `action` is private executable behavior inside an entity or system.
- `program` and `proc` describe orchestration structure.
