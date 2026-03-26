# Abide

> A specification language for executable, verifiable system behavior.

Abide lets you model system behavior formally — then simulate it, check it against properties, and prove guarantees. Specifications are readable enough to guide engineering decisions and precise enough for automated verification.

**Status:** Active design and implementation phase. Syntax and semantics are evolving. Early feedback is welcome.

## A Taste of Abide

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

verify paid_orders_can_ship for Commerce[0..50] {
  assert all o: Order |
    o.status == @Paid implies eventually (o.status == @Shipped)
}
```

## What Abide Covers

Abide spans five specification layers under one language:

1. **Structural modeling** — Define domain vocabulary with types, records, and algebraic data types. Model stateful objects as entities with fields and defaults.

2. **Behavioral modeling** — Specify state transitions with guarded actions (`requires`/`ensures`). Compose entities into systems with events. Express constraints as named predicates and properties.

3. **Temporal modeling** — Assert safety (`always`) and liveness (`eventually`) properties. Explore system behavior with bounded model checking. Construct scenario witnesses with `scene` blocks. Query specifications interactively with the [REPL](docs/repl.md) and [QA language](docs/qa-language.md) *(planned)*.

4. **Algorithm verification** *(planned)* — Verify function correctness with loop invariants, termination measures, and refinement types. Prove algorithms correct against their contracts.

5. **Proof escape hatch** *(planned)* — For properties beyond bounded checking, export proof obligations to a dependent type theory backend (Agda, Lean 4, or Rocq — under evaluation).

## Start Here

- **New to Abide?** Read the [Getting Started](docs/getting-started.md) guide
- **Want the syntax quickly?** See [Syntax at a Glance](docs/syntax-at-a-glance.md)
- **Evaluating the direction?** Read [Core Concepts](docs/core-concepts.md) and the [Roadmap](docs/roadmap.md)
- **Looking for examples?** See [Examples](docs/examples.md) and the `examples/` directory

## Design Influences

Abide draws directional inspiration from:

- **Alloy** — Lightweight structural modeling and bounded exploration
- **TLA+** — System-level temporal reasoning and state machine specification
- **Dafny / F\*** — Function and algorithm-level contracts with automated verification
- **Agda / Lean 4 / Rocq** — Dependent type theory for deep proof obligations

These are influences on the design, not compatibility guarantees.

## Repository Structure

```
compiler/    Compiler and checker implementation (Rust)
docs/        User-facing guides and references
examples/    Sample Abide specifications
stdlib/      Standard library (planned)
spec/        Language specification notes
```

## Building

Requires a Rust toolchain (stable).

```sh
cd compiler
cargo build --release
```

## Notes for Early Adopters

- This is not production-ready.
- Syntax, semantics, and file formats may change without notice.
- Issues and design feedback are welcome while the language is still being shaped.

## License

Released under Apache-2.0 with an added Commons Clause condition. See [LICENSE](LICENSE) for details.
