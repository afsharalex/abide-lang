# The Abide REPL

> Implemented in v0.

The Abide REPL is a live evaluation environment for interactive specification authoring and exploration. Modeled after Clojure's nREPL and Common Lisp's SLIME: load source files, experiment with definitions against a live universe, and switch to QA mode for instant structural queries.

## Core Principle: Files Are the Source of Truth

The REPL is **ephemeral**. Nothing entered in the REPL is saved to source files. You experiment freely — define entities, add actions, test ideas — and `/reload` discards everything and reloads from disk. The REPL is a scratchpad, not an editor.

## Two Modes

The REPL has two modes, switchable at any time:

| Mode | Prompt | Purpose |
|------|--------|---------|
| Abide mode (default) | `abide>` | Write and evaluate spec definitions and expressions |
| QA mode | `qa>` | Query the loaded specification (see [QA Language](qa-language.md)) |

Switch with `/qa` and `/abide`.

## Workflow

```
$ abide repl commerce/
Loaded module Commerce (3 entities, 1 system)

abide> entity Order {
.....>   action experimental_refund() requires status == @Confirmed {
.....>     status' = @Refunded
.....>   }
.....> }
OK — added action experimental_refund to Order (in-memory only)

abide> /qa
qa> ask reachable Order.status -> @Refunded
true
qa> explain path Order.status @Pending -> @Refunded
@Pending -> submit -> @Confirmed -> experimental_refund -> @Refunded
qa> /abide

abide> /reload
Reloaded from disk. In-memory changes discarded.

abide> /qa
qa> ask reachable Order.status -> @Refunded
false
```

**What happened:**
1. The REPL loaded all `.ab` files from `commerce/`
2. In Abide mode, a new `experimental_refund` action was added to `Order` — in memory only
3. Switching to QA mode, the query confirmed `@Refunded` is now reachable
4. `/reload` discarded the experiment and reloaded from disk
5. The same query now returns false — the refund action doesn't exist on disk

## Typical Use

1. Open `.ab` files in your editor
2. `abide repl commerce/` in a terminal — loads all modules, builds universe
3. Edit source files in your editor
4. `/reload` in the REPL picks up changes from disk
5. `/qa` for instant structural queries (reachability, terminals, paths, cycles)
6. Experimental definitions in Abide mode to test ideas without modifying files
7. `/reload` to discard experiments and return to the on-disk state

## Loading Behavior

```sh
abide repl                   # current directory (project config or scan for .ab files)
abide repl commerce/         # load a directory
abide repl order.ab       # load a file (+ dependencies)
```

| Target | Resolution |
|--------|-----------|
| No argument | Current directory — project config or scan for `.ab` files |
| Directory | Load all `.ab` files in the directory tree |
| Single file | Parse + follow `use`/`include` for dependencies |

## REPL Commands

| Command | Purpose |
|---------|---------|
| `/help` | Show available commands and syntax for current mode |
| `/quit` | Exit the REPL |
| `/reload` | Reload all files from disk, discard in-memory changes |
| `/verify` | Run verification against the current in-memory environment |
| `/simulate [options]` | Run one seeded forward simulation against the current in-memory environment |
| `/explore [options]` | Build a bounded operational state-space artifact |
| `/artifacts` | List stored native evidence, simulation, and state-space artifacts |
| `/show artifact <selector>` | Show artifact metadata and evidence summary |
| `/draw artifact <selector>` | Render a timeline view for temporal/operational artifacts |
| `/state artifact <selector> <n>` | Inspect a specific witness state |
| `/diff artifact <selector> <a> <b>` | Compare two witness states |
| `/export artifact <selector> json` | Print raw artifact JSON for one artifact |
| `/schema` | Show all loaded entities with fields and types |
| `/qa` | Switch to QA mode |
| `/abide` | Switch to Abide mode |

Artifact selectors can be a numeric session ID (`1`), a source name (`order_safety`), or a kind-qualified name (`counterexample:order_safety`). Plain names resolve to the latest stored artifact with that source name in the current session.

`/simulate` accepts the same controls as the CLI command, minus file arguments:

```text
/simulate [--steps N] [--seed N] [--slots N] [--scope Entity=N]... [--system NAME]
```

Simulation artifacts use the `simulation:<name>` selector form, where `<name>` is the explicit `--system` target when present or the first simulated system name otherwise.

`/explore` accepts:

```text
/explore [--depth N] [--slots N] [--scope Entity=N]... [--system NAME]
```

If `--depth` is omitted, the REPL enumerates the finite operational fragment exhaustively. State-space artifacts use the `state-space:<name>` selector form.

Artifacts are session-local. `/reload` and in-memory definition changes invalidate stored artifacts so you do not inspect evidence for an older program state by mistake.

## Keybindings

Emacs keybindings are the default (`Ctrl+A`, `Ctrl+E`, `Ctrl+K`, `Ctrl+R`, etc.). Use `--vi` for Vi mode:

```sh
abide repl --vi commerce/
```

Tab completion is context-aware:
- In QA mode: QA verbs → subcommands → entity/field/state names
- In Abide mode: keywords → definition names
- `@` prefix completes state atoms (`@Pending`, `@Shipped`)
- `Entity.` completes field names

## Multi-Line Input

Unbalanced braces or parentheses continue input on the next line:

```
abide> entity Order {
.....>   action refund() requires status == @Confirmed {
.....>     status' = @Refunded
.....>   }
.....> }
  OK: (added to in-memory environment)
```

`Ctrl+C` on a continuation line clears the buffer without exiting.

## Editor Integration

Editor integration (evaluate selections, inline results, QA from the editor) is provided by a separate LSP server (`abide-lsp`). See the editor integration documentation for details.

## How It Works

```
.ab files
    ↓ parse + elaborate + lower
Core IR (entities, transitions, systems)
    ↓ extract
FlowModel (state graphs, transition maps, reachability)
    ↓
REPL / QA query executor
```

The FlowModel is computed on load and rebuilt on `/reload` or after in-memory definitions. All QA queries execute against the FlowModel using graph traversals — no solver invocation, no file I/O. Responses are instant.

Abide mode definitions modify the in-memory IR and rebuild the FlowModel. They don't touch the file system.

`/verify` and `/simulate` use the current in-memory IR, not just the on-disk files. Evidence-bearing verification results and simulation runs are stored as native session-local artifacts. The artifact commands operate on those native objects rather than on flattened terminal output.

Today, the REPL stores:
- evidence-bearing verification results that already emit native evidence objects: counterexamples, liveness violations, deadlocks, and admitted proof-artifact references
- native simulation runs produced by `/simulate`
- bounded operational state spaces produced by `/explore`

Scene results are still printed by `/verify`, but they do not yet produce native artifacts.
