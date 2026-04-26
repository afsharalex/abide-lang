# Abide Documentation

## Reading Paths

**Evaluating Abide?** Start with [Core Concepts](core-concepts.md) for the mental model, then skim [Syntax at a Glance](syntax-at-a-glance.md) and the [Roadmap](roadmap.md).

**Writing your first spec?** Follow [Getting Started](getting-started.md), then use [Syntax at a Glance](syntax-at-a-glance.md) as a reference while working through [Examples](examples.md).

**Running Abide from the CLI?** Read [CLI Reference](cli.md) for the current command surface, including `verify`, `simulate`, `qa`, and the REPL.

**Understanding the design?** Read [Core Concepts](core-concepts.md) for the five specification layers, then explore the `examples/` directory for real specs.

## Pages

| Page | Description |
|------|-------------|
| [Getting Started](getting-started.md) | Build the compiler, write and check your first spec |
| [Syntax at a Glance](syntax-at-a-glance.md) | One-page cheat sheet with compact examples |
| [Core Concepts](core-concepts.md) | The five specification layers and how they fit together |
| [Examples](examples.md) | Curated examples with commentary |
| [CLI Reference](cli.md) | Current command surface, flags, reporting modes, and file conventions |
| [REPL](repl.md) | Interactive specification authoring, verification, simulation, and artifact exploration |
| [QA Language](qa-language.md) | Structural query language plus verification/simulation artifact scripting |
| [Roadmap](roadmap.md) | What works now, what's next, what's deferred |
| [Error Reference](errors.md) | Error codes (E001–E010), descriptions, and fix guidance |
| [FAQ](faq.md) | Common questions and clarifications |

## Maturity

Abide is usable now for a meaningful bounded-verification and interactive-exploration slice, but the language and backend architecture are still evolving. The constructs marked **Stable** in [Syntax at a Glance](syntax-at-a-glance.md) are unlikely to change significantly. Constructs marked **Evolving** may change in syntax or semantics. Constructs marked **Planned** are designed but not yet implemented.
