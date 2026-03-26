# CLI Reference

## Current Usage

```
abide [OPTIONS] <FILE>
```

The compiler takes a single `.abide` source file and runs the requested pipeline stage.

### Options

| Flag | Description |
|------|-------------|
| `--lex-only` | Tokenize the file and print tokens with spans |
| `--parse-only` | Parse the file and print the AST |
| `--elaborate-only` | Run elaboration (type checking and resolution) |
| `--emit-ir` | Run the full frontend pipeline and emit IR as JSON |
| `-h, --help` | Print help |

Running `abide <file>` without flags currently prints:

```
full pipeline not yet implemented — use --lex-only or --parse-only
```

### Examples

**Parse a spec and check for syntax errors:**

```sh
$ abide --parse-only examples/order.abide
```

If the file is well-formed, the compiler prints the AST. If there's a syntax error, it reports the location:

```
Error: abide::parse::expected
  × expected `:`, found `,`
```

**Emit IR as JSON:**

```sh
$ abide --emit-ir examples/order.abide
```

Produces a JSON representation of the elaborated specification:

```json
{
  "types": [
    {
      "name": "OrderStatus",
      "type": {
        "tag": "Enum",
        "name": "OrderStatus",
        "constructors": ["Pending", "Paid", "Shipped"]
      }
    }
  ],
  "entities": [
    {
      "name": "Order",
      "fields": [
        { "name": "id", "type": { "tag": "Id" }, "default": null },
        ...
      ],
      "actions": [ ... ]
    }
  ],
  "systems": [ ... ]
}
```

**Tokenize only (for debugging):**

```sh
$ abide --lex-only examples/order.abide
```

Prints each token with its source span:

```
Span { start: 99, end: 103 }  type
Span { start: 104, end: 115 }  OrderStatus
Span { start: 116, end: 117 }  =
...
```

---

## Planned Commands

The following subcommands are planned but not yet implemented. This section describes the intended CLI surface.

### `abide check`

Type-check a specification file or project.

```sh
$ abide check spec.abide
$ abide check .                    # check all .abide files in directory
```

Validates types, entity fields, action guards, system composition, and name resolution. Reports errors and warnings. This will be the default command for day-to-day spec authoring.

### `abide verify`

Run bounded model checking and automated unbounded proof attempts on `verify` blocks.

```sh
$ abide verify spec.abide
$ abide verify spec.abide --unbounded-only
$ abide verify spec.abide --bounded-only
```

Expected output:

```
Checking "no overdraft" for Banking[0..500]...
  PROVED (inductive invariant, 0.3s)

Checking "eventual delivery" for Commerce[0..100]...
  CHECKED to depth 100 (no counterexample found, 1.2s)
  Note: could not prove unboundedly — checked to specified bound only

Checking "invalid transition" for Commerce[0..50]...
  COUNTEREXAMPLE (3 steps):
    t=0: Commerce::submit_order(order1) → Order.status: @Pending → @AwaitingPayment
    t=1: Commerce::ship_order(order1)   → BLOCKED (requires status == @Paid)
```

The solver attempts unbounded proof first, falls back to bounded checking, and reports counterexample traces on failure.

### `abide proof`

Check proof obligations in `.proof.abide` files against external backends.

```sh
$ abide proof spec.proof.abide
$ abide proof spec.proof.abide --backend agda
```

Exports proof obligations to the configured backend (Agda, Lean 4, or Rocq) and reports whether they verify.

### `abide repl`

Interactive specification authoring and querying.

```sh
$ abide repl
$ abide repl --port 7888           # nREPL server mode for editor integration
```

Two modes:
- `/abide` — write and evaluate spec fragments interactively
- `/qa` — query the loaded specification (`ask`, `explain`, `assert`)

### `abide simulate`

Forward-simulate random event sequences without the solver.

```sh
$ abide simulate spec.abide --steps 50 --seed 42
```

Picks random enabled events, applies them, and prints an Event Calculus-style trace. Useful for exploring system behavior interactively.

### `abide qa`

Run QA scripts for CI/CD.

```sh
$ abide qa checks.qa
```

Executes scriptable structural checks (`ask`, `explain`, `assert` commands) against a specification.

---

## File Conventions

| Extension | Purpose | Relevant command |
|-----------|---------|------------------|
| `.abide` | Definitions (types, entities, systems, functions) | `check` |
| `.spec.abide` | Verification (verify, scene blocks) | `verify` |
| `.proof.abide` | Proofs (proof, lemma blocks) | `proof` |
| `.qa` | QA scripts | `qa` |

These extensions are conventions, not enforced — the CLI subcommand determines execution mode, not the file extension.
