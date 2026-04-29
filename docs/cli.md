# CLI Reference

The `abide` binary exposes these subcommands:

- `lex`
- `parse`
- `elaborate`
- `emit-ir`
- `export-temporal`
- `verify`
- `run`
- `simulate`
- `trace`
- `qa`
- `repl`

## `abide lex`

Lex a source file and print tokens.

```sh
abide lex spec.ab
```

## `abide parse`

Parse a source file and print the AST.

```sh
abide parse spec.ab
```

## `abide elaborate`

Load one or more files, resolve names, and print elaborated output.

```sh
abide elaborate types.ab system.ab checks.ab
```

## `abide emit-ir`

Emit the lowered IR as JSON.

```sh
abide emit-ir spec.ab
```

## `abide export-temporal`

Export compiled temporal formulas for verify blocks as JSON.

```sh
abide export-temporal spec.ab
```

## `abide verify`

Run verification across verify blocks, scenes, theorems, props, and function contracts.

```sh
abide verify spec.ab
abide verify spec.ab --solver auto --progress
abide verify spec.ab --bounded-only
abide verify spec.ab --report json reports/
```

Selected flags:

- `--solver {z3,cvc5,auto,both}`
- `--chc-solver {z3,cvc5,auto}`
- `--bounded-only`
- `--unbounded-only`
- `--timeout <secs>`
- `--induction-timeout <secs>`
- `--bmc-timeout <secs>`
- `--ic3-timeout <secs>`
- `--no-ic3`
- `--no-prop-verify`
- `--no-fn-verify`
- `--no-relational-symmetry-breaking`
- `--progress`
- `--witness-semantics {operational,relational}`
- `--verbose`
- `--debug-evidence`
- `--report <format> [output_dir]`
- `--target <target>`
- `--trace-artifact <path>`

## `abide run`

Run one seeded model execution without the solver.

```sh
abide run spec.ab --steps 25
abide run spec.ab --seed 7 --slots 8
abide run spec.ab --scope Order=12 --system Commerce
abide run spec.ab --trace-artifact traces/run.json
```

Selected flags:

- `--steps <n>`
- `--seed <n>`
- `--slots <n>`
- `--scope Entity=SLOTS`
- `--system <name>`
- `--trace-artifact <path>`

## `abide simulate`

`simulate` has the same behavior and flags as `run`.

## `abide trace`

Inspect structured artifacts emitted by `verify --trace-artifact` or `run --trace-artifact`.

```sh
abide trace traces/run.json
abide trace traces/run.json draw
abide trace traces/run.json state 1
abide trace traces/run.json diff 0 1
abide trace traces/run.json --artifact 2 json
```

Subcommands:

- `list`
- `draw`
- `state <index>`
- `diff <from> <to>`
- `json`

`draw` prints selected transitions, nondeterministic choices, observations, and state changes. Liveness artifacts are lasso-shaped when native liveness evidence is available; `list`, `draw`, and `state` show the loop-start frame.

Flags:

- `--artifact <id>`

## `abide qa`

Run QA scripts.

```sh
abide qa checks.qa -f .
abide qa checks.qa -f specs --format json
```

Flags:

- `-f, --from <dir>`
- `--format {human,json}`

## `abide repl`

Start the interactive REPL.

```sh
abide repl
abide repl .
abide repl . --vi
```

## File conventions

Current command behavior is driven by the subcommand, not the extension.

Common conventions:

| Extension | Typical use |
| --- | --- |
| `.ab` | Abide source files |
| `.qa` | QA scripts |

Multiple `.ab` files can be passed together to `elaborate`, `emit-ir`, or `verify`.
