# CLI Reference

## Usage

```
abide <COMMAND> <FILE> [OPTIONS]
```

The compiler uses subcommands. Each takes a single `.abide` source file.

### Implemented Commands

| Command | Description |
|---------|-------------|
| `abide lex <file>` | Tokenize the file and print tokens with spans |
| `abide parse <file>` | Parse the file and print the AST |
| `abide elaborate <file>` | Run elaboration (type checking and resolution) |
| `abide emit-ir <file>` | Run the full frontend pipeline and emit IR as JSON |
| `abide verify <file>` | Verify: bounded model checking, scene checking, theorem proving |

### `abide verify` Options

| Flag | Description |
|------|-------------|
| `--bounded-only` | Skip induction (Tier 1), only run BMC |
| `--unbounded-only` | Skip BMC (Tier 2), only try induction |
| `--induction-timeout <N>` | Induction timeout in seconds (default: 5) |
| `--bmc-timeout <N>` | BMC timeout in seconds (default: 0 = no timeout) |
| `--progress` | Print progress messages to stderr during verification |

The `--bounded-only` and `--unbounded-only` flags are mutually exclusive.

### Examples

**Verify a spec with tiered dispatch (induction → BMC fallback):**

```sh
$ abide verify examples/order.abide
PROVED  order_safety (method: 1-induction, 35ms)
CHECKED liveness_check (depth: 10, 200ms)
PASS    happy_path (3ms)
```

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
