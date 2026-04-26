# CLI Reference

## Usage

```
abide <COMMAND> <FILE...> [OPTIONS]
```

The compiler uses subcommands. Most commands accept one or more `.ab` source files. When multiple files are provided, the compiler loads them all into a shared environment, resolves `include` directives transitively, and applies module-scoped `use` declarations before elaboration.

### Implemented Commands

| Command | Description |
|---------|-------------|
| `abide lex <file>` | Tokenize a file and print tokens with spans |
| `abide parse <file>` | Parse a file and print the AST |
| `abide elaborate <files...>` | Load file(s), run elaboration (collection, resolution, checking) |
| `abide emit-ir <files...>` | Load file(s), run the full frontend pipeline and emit IR as JSON |
| `abide export-temporal <files...>` | Load file(s) and emit compiled temporal summaries for `verify` blocks as JSON |
| `abide verify <files...>` | Load file(s), verify: model checking, scene checking, theorem proving |
| `abide simulate <files...>` | Load file(s), run one seeded forward simulation over the executable fragment |
| `abide qa <script.qa>` | Run QA structural analysis script |
| `abide repl [path]` | Start interactive REPL |

### `abide qa` Options

| Flag | Description |
|------|-------------|
| `-f, --from <path>` | Load specs from this directory or file before running the script |
| `--format <human\|json>` | Output format (default: human) |

### `abide repl` Options

| Flag | Description |
|------|-------------|
| `--vi` | Use Vi keybindings instead of Emacs |

### `abide verify` Options

| Flag | Description |
|------|-------------|
| `--bounded-only` | Skip induction and IC3 (Tier 1), only run BMC |
| `--unbounded-only` | Skip BMC (Tier 2), only try induction and IC3 |
| `--timeout <N>` | End-to-end verify timeout in seconds (default: 1200, `0` = no timeout) |
| `--induction-timeout <N>` | Induction timeout in seconds (default: 1200, `0` = no timeout) |
| `--bmc-timeout <N>` | BMC timeout in seconds (default: 1200, `0` = no timeout) |
| `--ic3-timeout <N>` | IC3/PDR timeout in seconds (default: 1200, `0` = no timeout) |
| `--no-ic3` | Skip IC3/PDR verification (for speed) |
| `--no-prop-verify` | Skip automatic prop verification |
| `--no-fn-verify` | Skip function contract verification |
| `--progress` | Print progress messages to stderr during verification |
| `--witness-semantics <operational\|relational>` | Choose the native witness family for failing verification results |
| `--verbose` | Print expanded human-readable verification details |
| `--debug-evidence` | Dump raw native evidence JSON to the terminal for debugging |
| `--report <format> [output_dir]` | Write a verification report as `json`, `html`, or `markdown`; defaults to `reports/` |

The `--bounded-only` and `--unbounded-only` flags are mutually exclusive.
`--verbose` affects terminal output only. `--report` writes artifacts to disk
using a derived file name: a single-file run uses `<stem>.report.<ext>`, while
multi-file runs use `verification-report.<ext>`.
`--debug-evidence` is the explicit escape hatch for raw JSON dumps; human
terminal and report formats render structured views instead.

### Examples

**Verify a spec with tiered dispatch (induction → IC3 → BMC fallback):**

```sh
$ abide verify examples/order.ab
PROVED  order_safety (method: 1-induction, 35ms)
PROVED  complex_invariant (method: IC3/PDR, 1200ms)
CHECKED liveness_check (depth: 10, 200ms)
PASS    happy_path (3ms)
```

**Verify functions with contracts (postconditions, termination, call-site preconditions):**

```sh
$ abide verify examples/algorithms.ab
PROVED  fn factorial (contract, 18ms)
PROVED  fn gcd (contract, 5ms)
```

**Functions with `assume` report ADMITTED, functions with `sorry` skip verification:**

```sh
$ abide verify spec.ab
PROVED   fn verified_fn (contract, 12ms)
ADMITTED fn uses_assume (assume in body, 3ms)
ADMITTED fn placeholder (sorry in body, 0ms)
```

Function contracts (`requires`/`ensures`/`decreases`) are verified automatically as part of `abide verify`. Use `--no-fn-verify` to skip this for faster iteration on system-level properties.

**Verify multiple files together (multi-module):**

```sh
$ abide verify src/commerce.ab src/billing.ab src/spec.ab
```

The compiler loads all files, each declaring its own module. `use` declarations bring cross-module names into scope. `include` directives are resolved relative to the including file.

**Inspect native evidence while working locally:**

```sh
$ abide verify tests/fixtures/fairness.ab --verbose
```

This keeps the normal human-readable verification output and adds expanded
details such as source location, assumptions, and evidence kind.

**Dump raw evidence JSON for debugging:**

```sh
$ abide verify tests/fixtures/fairness.ab --debug-evidence
```

This is a debug surface, not the normal human-readable presentation.

**Write a JSON report to the default `reports/` directory:**

```sh
$ abide verify tests/fixtures/fairness.ab --report json
```

This writes `reports/fairness.report.json` for a single input file.

**Write a report to a specific directory:**

```sh
$ abide verify tests/fixtures/fairness.ab --report html out/
```

This writes `out/fairness.report.html`.

**Generate a Markdown report while keeping compact terminal output:**

```sh
$ abide verify tests/fixtures/fairness.ab --report markdown
```

Reports include diagnostics, result summaries, and native evidence payloads.

### `abide simulate` Options

| Flag | Description |
|------|-------------|
| `--steps <N>` | Maximum number of scheduled steps to execute |
| `--seed <N>` | Seed for deterministic scheduling |
| `--slots <N>` | Default pool size to preallocate per entity type |
| `--scope <Entity=N>` | Override the default pool size for a specific entity type; may be repeated |
| `--system <NAME>` | Restrict top-level scheduling to the named root system |

`abide simulate` runs one seeded forward execution over the current executable
fragment. It is a debugging and exploration tool, not an explicit-state model
checker and not an exhaustive bounded search engine.

**Run one seeded simulation:**

```sh
$ abide simulate examples/order.ab --steps 50 --seed 42 --slots 4
```

**Override pool sizes for selected entities:**

```sh
$ abide simulate examples/banking.ab --system Banking --steps 25 --scope Account=8 --scope Transfer=2
```

**Parse a spec and check for syntax errors:**

```sh
$ abide parse examples/order.ab
```

**Emit IR as JSON:**

```sh
$ abide emit-ir examples/order.ab
```

**Export compiled temporal summaries for `verify` blocks:**

```sh
$ abide export-temporal examples/workflow.ab
```

This emits JSON for each `verify` block's asserts, including whether the assert
contains temporal or liveness structure and, for the current supported
future-time fragment, a Spot-style formula export with opaque atom bindings.

---

## Planned Commands

The following command surfaces are still planned or intentionally deferred.

### `abide check`

Type-check a specification file or project.

```sh
$ abide check spec.ab
$ abide check .                    # check all .ab files in directory
```

Validates types, entity fields, action guards, system composition, and name resolution. Reports errors and warnings. This will be the default command for day-to-day spec authoring.

### `abide proof`

Check proof obligations in `.proof.ab` files against external backends.

```sh
$ abide proof spec.proof.ab
$ abide proof spec.proof.ab --backend agda
```

Exports proof obligations to the configured backend (Agda, Lean 4, or Rocq) and reports whether they verify.

### Follow-on work in existing commands

- `abide verify`
  - proof-manager / proof-backend routing
  - scene artifacts as first-class native artifacts
  - broader non-Z3 backend coverage
- `abide repl`
  - editor/LSP integration rather than terminal-only use
- `abide simulate`
  - explicit-state exploration is a separate future backend, not an extension of the current simulator
- `abide qa`
  - richer result families once scenes and future backends emit native artifacts

---

## File Conventions

| Extension | Purpose | Relevant command |
|-----------|---------|------------------|
| `.ab` | Definitions (types, entities, systems, functions) | `check` |
| `.spec.ab` | Verification (verify, scene blocks) | `verify` |
| `.proof.ab` | Proofs (theorem, lemma blocks) | `proof` |
| `.qa` | QA scripts | `qa` |

These extensions are conventions, not enforced — the CLI subcommand determines execution mode, not the file extension.
