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
abide verify spec.ab --solver auto --stream
abide verify spec.ab --bounded-only
abide verify spec.ab --report json reports/
abide verify examples/relations.ab --witness-semantics relational
```

Selected flags:

- `--solver {z3,cvc5,auto,both}`
- `--chc-solver {z3,cvc5,auto}`
- `--bounded-only`
- `--unbounded-only`
- `--timeout <secs>`
- `--induction-timeout <secs>`
- `--bmc-timeout <secs>`
- `--prop-bmc-depth <depth>`
- `--no-bmc-iterative-deepening`
- `--ic3-timeout <secs>`
- `--ic3`
- `--cvc5-sygus`
- `--no-prop-verify`
- `--no-fn-verify`
- `--no-relational-symmetry-breaking`
- `--stream` — print completed verification results as targets finish
- `--witness-semantics {operational,relational}`
- `--verbose`
- `--debug-evidence`
- `--report <format> [output_dir]`
- `--target <target>`
- `--trace-artifact <path>`

`CHECKED` is the bounded trace-prefix result kind. It means no counterexample
was found within the explored transition depth. The depth can include stutter
steps, and it is not exhaustive reachable-state exploration or all-instance
coverage.

Human `verify` output is formatted for terminal scanning. Each result row
shows verdict, target, duration, and detail columns. Long detail text wraps
under the detail column, and wrapped rows are separated with a blank line.
When the terminal supports color, successful verdicts such as `PROVED`,
`CHECKED`, and `PASS` are green; trusted or admitted verdicts are yellow; and
failing verdicts such as `COUNTEREXAMPLE`, `UNPROVABLE`, `FAILED`, `DEADLOCK`,
and liveness violations are red. Captured or piped output is kept plain.

Do not parse human terminal output for automation. Use `--report json`,
`--report markdown`, `--report html`, or `--trace-artifact` when scripts need
stable machine-readable verification results or evidence.

Ordinary `verify` runs bounded/exploration checking by default with a
30-second end-to-end timeout. When a bounded `CHECKED` result may need an
unbounded proof attempt, Abide reports that and suggests an explicit proof-mode
rerun. Use `--ic3` to opt verify blocks into IC3/PDR proof search, or
`--unbounded-only` when you want proof search without the bounded fallback.
Scenes and `run`/`simulate` remain bounded/execution workflows and do not use
proof engines.

Safety BMC searches depths incrementally by default so counterexamples stop at
the first failing bound. Use `--no-bmc-iterative-deepening` to run the selected
bound as one solver query.

Props are first tried with the proof-oriented tiers. If a prop falls back to
bounded checking, `--prop-bmc-depth` controls that fallback depth.

`--solver cvc5` can use cvc5 for supported SMT checks. In-process cvc5
SyGuS invariant synthesis is disabled by default because the cvc5 Rust API
does not provide a hard cancellation hook. Use `--solver cvc5 --cvc5-sygus`
or `--solver both --cvc5-sygus` only for isolated proof experiments. Unsupported
SyGuS fragments report `Unprovable` under `--unbounded-only`; otherwise the
verifier falls back to the ordinary bounded tiers instead of claiming a proof.

Relation counterexamples use the normal verify result path. With relational
witness evidence available, human output shows derived tuple sets and JSON
reports include the same witness envelope.

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
