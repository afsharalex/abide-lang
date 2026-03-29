# CLI Reference

## Usage

```
abide <COMMAND> <FILE...> [OPTIONS]
```

The compiler uses subcommands. Most commands accept one or more `.abide` source files. When multiple files are provided, the compiler loads them all into a shared environment, resolves `include` directives transitively, and applies module-scoped `use` declarations before elaboration.

### Implemented Commands

| Command | Description |
|---------|-------------|
| `abide lex <file>` | Tokenize a file and print tokens with spans |
| `abide parse <file>` | Parse a file and print the AST |
| `abide elaborate <files...>` | Load file(s), run elaboration (collection, resolution, checking) |
| `abide emit-ir <files...>` | Load file(s), run the full frontend pipeline and emit IR as JSON |
| `abide verify <files...>` | Load file(s), verify: model checking, scene checking, theorem proving |

### `abide verify` Options

| Flag | Description |
|------|-------------|
| `--bounded-only` | Skip induction and IC3 (Tier 1), only run BMC |
| `--unbounded-only` | Skip BMC (Tier 2), only try induction and IC3 |
| `--induction-timeout <N>` | Induction timeout in seconds (default: 5) |
| `--bmc-timeout <N>` | BMC timeout in seconds (default: 0 = no timeout) |
| `--ic3-timeout <N>` | IC3/PDR timeout in seconds (default: 10) |
| `--no-ic3` | Skip IC3/PDR verification (for speed) |
| `--no-prop-verify` | Skip automatic prop verification |
| `--progress` | Print progress messages to stderr during verification |

The `--bounded-only` and `--unbounded-only` flags are mutually exclusive.

### Examples

**Verify a spec with tiered dispatch (induction → IC3 → BMC fallback):**

```sh
$ abide verify examples/order.abide
PROVED  order_safety (method: 1-induction, 35ms)
PROVED  complex_invariant (method: IC3/PDR, 1200ms)
CHECKED liveness_check (depth: 10, 200ms)
PASS    happy_path (3ms)
```

**Verify multiple files together (multi-module):**

```sh
$ abide verify src/commerce.abide src/billing.abide src/spec.abide
```

The compiler loads all files, each declaring its own module. `use` declarations bring cross-module names into scope. `include` directives are resolved relative to the including file.

**Parse a spec and check for syntax errors:**

```sh
$ abide parse examples/order.abide
```

**Emit IR as JSON:**

```sh
$ abide emit-ir examples/order.abide
```

---

## Planned Commands

The following subcommands are planned but not yet implemented.

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
Checking no_overdraft for Banking[0..500]...
  PROVED (inductive invariant, 0.3s)

Checking eventual_delivery for Commerce[0..100]...
  CHECKED to depth 100 (no counterexample found, 1.2s)
  Note: could not prove unboundedly — checked to specified bound only

Checking invalid_transition for Commerce[0..50]...
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
| `.proof.abide` | Proofs (theorem, lemma blocks) | `proof` |
| `.qa` | QA scripts | `qa` |

These extensions are conventions, not enforced — the CLI subcommand determines execution mode, not the file extension.
