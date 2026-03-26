# Getting Started

> Abide is under heavy development. The syntax and semantics will change frequently. We will announce when an alpha release with solver backend support is available.

## Prerequisites

- Rust toolchain (stable) — install via [rustup.rs](https://rustup.rs)

## Build

```sh
git clone https://github.com/afsharalex/abide-lang.git
cd abide-lang/compiler
cargo build --release
```

The binary is at `target/release/abide`.

## Write Your First Spec

Create a file called `order.abide`:

```abide
type OrderStatus = Pending | Paid | Shipped

entity Order {
  id: Id
  status: OrderStatus = @Pending
  total: Real

  action pay() requires status == @Pending requires total > 0 {
    status' = @Paid
  }

  action ship() requires status == @Paid {
    status' = @Shipped
  }
}

system Commerce {
  use Order

  event place_order(o: Order) requires o.status == @Pending {
    o.pay()
  }
}
```

## Check It

```sh
abide --parse-only order.abide
```

If the spec parses correctly, the compiler prints the AST. If there's a syntax error, it points to the offending line.

> **Note:** The full pipeline (`abide order.abide`) is not yet implemented. Current available flags:
> - `--lex-only` — tokenize and print tokens
> - `--parse-only` — parse and print AST
> - `--elaborate-only` — run elaboration
> - `--emit-ir` — emit IR as JSON

## What Just Happened

You defined:

- A **type** (`OrderStatus`) — an enum with three states
- An **entity** (`Order`) — a stateful domain object with fields and defaults
- Two **actions** (`pay`, `ship`) — guarded state transitions using primed notation (`status' = @Paid` means "the next value of status is Paid")
- A **system** (`Commerce`) — a boundary that composes entities and defines events
- An **event** (`place_order`) — an externally triggered action with a precondition

The `@` prefix marks state atoms (`@Pending`, `@Paid`). The prime notation (`'`) distinguishes current state from next state — this is how Abide expresses state transitions without mutation.

## Add Verification

Append this to your file:

```abide
verify "order lifecycle" for Commerce[0..50] {
  assert always (all o: Order |
    o.status == @Shipped implies o.total > 0)
}

scene "successful payment" for Commerce {
  given let o = one Order where o.status == @Pending and o.total == 100
  when action p = Commerce::place_order(o) { one }
  then assert o.status == @Paid
}
```

The `verify` block will ask the bounded model checker to explore up to 50 steps of the Commerce system and confirm the assertion holds on every reachable state. The solver backend is in development — for now, the compiler parses and type-checks the verify block but does not yet run the solver.

The `scene` block constructs a concrete scenario: given an order in a specific state, when a specific event fires, then a specific outcome holds. Scenes are existential witnesses — they demonstrate that a behavior is possible. Like verify blocks, scenes are parsed and type-checked now; solver-backed execution is planned.

## Next Steps

- [Syntax at a Glance](syntax-at-a-glance.md) — quick reference for all constructs
- [Core Concepts](core-concepts.md) — the five specification layers
- [Examples](examples.md) — more specs to learn from
