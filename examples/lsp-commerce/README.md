# LSP Commerce Example

This directory is a deliberately multi-file Abide project for exercising
project-aware LSP behavior and the current CLI/QA workflows.

Abide does not currently use a project manifest such as `abide.toml` or
`pact.toml`. The project boundary here is the directory, and `src/project.ab`
is the single `program` root that wires the workflows across the source tree.

## Layout

```text
src/
  project.ab
  domain/
    order.ab
    payment.ab
    inventory.ab
    shipment.ab
  systems/
    storefront.ab
  policies/
    safety.ab
qa/
  structure.qa
  hypotheticals.qa
```

The source files intentionally span several modules and use imports, aliases,
contracts, state transitions, reusable proc DAGs, an inline program proc,
scenes, and bounded verification blocks. The `project.ab` file is the program
root; the QA scripts load it and ask structural questions that are useful when
testing completion, diagnostics, symbol lookup, and CLI behavior.

## Commands

From `abide-lang`:

```sh
cargo run -p abide -- elaborate examples/lsp-commerce/src/project.ab
cargo run -p abide -- qa examples/lsp-commerce/qa/structure.qa
cargo run -p abide -- qa examples/lsp-commerce/qa/hypotheticals.qa
```

And to verify:

```sh
cargo run -p abide -- verify examples/lsp-commerce/src/project.ab
```

Or, to prove:

```sh
cargo run -p abide -- verify examples/lsp-commerce/src/project.ab --ic3
```
