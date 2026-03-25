# abide-lang

> Abide turns system behavior into an executable, verifiable contract.  
> Model what must be true, explore it in motion, and keep specs readable enough to guide real engineering decisions.

Abide is a formal specification language for practical engineering: an executable, verifiable contract for system behavior.

Write specifications you can simulate and check, while keeping them readable for humans and aligned with real implementations.

**Status:** active design/implementation phase; syntax and semantics are still evolving.

## Language goals

Abide is being designed as a specification language for defining system behavior that is:

1. executable (simulation and trace generation),
2. verifiable (bounded and unbounded claims),
3. documentable (human-readable specifications), and
4. exportable (canonical IR for conformance checking).

In short: write one specification that supports exploration, proof obligations, and implementation conformance workflows.

### Experience goals

Beyond formal capability, Abide is also aiming for strong developer ergonomics:

- Fast modeling and iteration loops, not proof-heavy ceremony for every task.
- Interactive workflows via a live REPL and incremental model updates.
- Exploratory analysis tooling (simulation/trace style workflows) alongside verification.
- Queryable model state for debugging and understanding behavior.

### Design influences (directional)

Current language and tooling direction draws inspiration from:

- Alloy-style lightweight modeling and exploration,
- TLA+-style system and concurrency reasoning,
- Dafny-style algorithm/function-level precision where needed,
- optional deeper type-theoretic guarantees for critical slices (DTT).

These are design influences, not compatibility guarantees.

## What this repository includes

- `compiler/`: CLI/compiler implementation.
- `stdlib/`: standard library modules and checks.
- `examples/`: sample Abide projects (will evolve as syntax stabilizes).
- `docs/`: user-facing guides and references.
- `spec/`: language contract notes and IR snapshots.

## Notes for early adopters

- This is not production-ready yet.
- Syntax, APIs, and file formats may change without notice.
- Issues and design feedback are welcome while the language is still being shaped.

## Repository and licensing notes

- Repository hosting location may change as the project setup is finalized.
- This repository is released under Apache-2.0 with an added Commons Clause condition (see `LICENSE`).
