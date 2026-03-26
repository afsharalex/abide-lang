# The Abide REPL

> Planned feature — not yet implemented.

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
1. The REPL loaded all `.abide` files from `commerce/`
2. In Abide mode, a new `experimental_refund` action was added to `Order` — in memory only
3. Switching to QA mode, the query confirmed `@Refunded` is now reachable
4. `/reload` discarded the experiment and reloaded from disk
5. The same query now returns false — the refund action doesn't exist on disk

## Typical Use

1. Open `.abide` files in your editor
2. `abide repl commerce/` in a terminal — loads all modules, builds universe
3. Edit source files in your editor
4. `/reload` in the REPL picks up changes from disk
5. `/qa` for instant structural queries (reachability, terminals, paths, cycles)
6. Experimental definitions in Abide mode to test ideas without modifying files
7. `/reload` to discard experiments and return to the on-disk state

## Loading Behavior

```sh
abide repl                   # current directory (project config or scan for .abide files)
abide repl commerce/         # load a directory
abide repl order.abide       # load a file (+ dependencies)
```

| Target | Resolution |
|--------|-----------|
| No argument | Current directory — project config or scan for `.abide` files |
| Directory | Load all `.abide` files in the directory tree |
| Single file | Parse + follow `use`/`include` for dependencies |

## REPL Commands

| Command | Purpose |
|---------|---------|
| `/help` | Show available commands and syntax for current mode |
| `/quit` | Exit the REPL |
| `/reload` | Reload all files from disk, discard in-memory changes |
| `/schema` | Show all loaded entities with fields and types |
| `/qa` | Switch to QA mode |
| `/abide` | Switch to Abide mode |

## Editor Integration (nREPL Server)

The REPL supports a server mode for editor integration:

```sh
abide repl --port 7888       # start nREPL server (editor connects)
abide repl                   # start interactive TUI (default)
```

The server accepts the same commands as the interactive REPL. Editor plugins (VS Code, Emacs, Neovim) connect and send/receive structured messages. This enables:

- Evaluate a selection from an `.abide` file in the live universe
- Run QA queries and display results inline
- Auto-reload on file save

## How It Works

```
.abide files
    ↓ parse + elaborate + lower
Core IR (entities, transitions, systems)
    ↓ extract
FlowModel (state graphs, transition maps, reachability)
    ↓
REPL / QA query executor
```

The FlowModel is computed on load and rebuilt on `/reload` or after in-memory definitions. All QA queries execute against the FlowModel using graph traversals — no solver invocation, no file I/O. Responses are instant.

Abide mode definitions modify the in-memory IR and rebuild the FlowModel. They don't touch the file system.
