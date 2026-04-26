# The QA Language

> Implemented in v0.

QA (Query Abide) is a small, purpose-built language for querying specifications structurally. It answers questions about your spec without running the solver — what states are reachable, where are the cycles, what transitions exist, what events touch a field.

QA runs in two contexts:
- **Interactive** — via `/qa` mode in the [REPL](repl.md)
- **Scripted** — via `abide qa script.qa` for CI/CD

## Statement Types

| Statement | Purpose | Output |
|-----------|---------|--------|
| `ask <query>` | Query, print result | Informational |
| `explain <query>` | Query with reasoning trace | Verbose informational |
| `assert <query>` | Query, fail if false | CI/CD gate (non-zero exit) |
| `load "path"` | Load specs from file or directory | N/A (scripts only) |
| `verify` | Run verification on the current in-memory spec and store evidence-bearing results as artifacts | Verification results + stored artifacts |
| `simulate [options]` | Run one seeded forward simulation and store the run as an artifact | Simulation summary + stored artifact |
| `artifacts` | List stored artifacts from earlier `verify` or `simulate` statements | Artifact summaries |
| `show artifact <selector>` | Show artifact metadata and evidence summary | Artifact details |
| `draw artifact <selector>` | Draw a timeline view when the artifact is temporal | Timeline |
| `state artifact <selector> <n>` | Inspect a specific artifact state | State dump |
| `diff artifact <selector> <a> <b>` | Compare two artifact states | State diff |
| `export artifact <selector> json` | Print raw artifact JSON | JSON |

## Query Vocabulary

### State Machine Queries

```
ask terminal Order.status                    // sink states (no outgoing transitions)
ask initial Order.status                     // source states (default values)
ask reachable Order.status -> @Shipped       // can @Shipped be reached?
ask path Order.status @Pending -> @Shipped   // transition path between states
ask cycles Order.status                      // circular transitions
ask transitions from Order.status == @Paid   // outgoing transitions from @Paid
```

These queries operate on the entity's state graph — the graph of possible transitions derived from actions and their guards.

### Discovery Queries

```
ask entities                                 // list all entities
ask systems                                  // list all systems
ask types                                    // list all types
ask invariants on Account                    // entity invariants and properties
ask contracts on Account.deposit             // requires/ensures on an action
ask events on Order.status                   // which events touch this field
ask match-coverage Order.status              // match arm completeness
```

### Cross-System Queries

```
ask cross-calls from Commerce                // outgoing cross-system event calls
ask updates on Order.status @Pending -> @Paid  // what causes this transition
```

### Diagnostic Queries (`explain`)

`explain` gives the reasoning behind a result — not just the answer, but why:

```
explain reachable Order.status -> @Shipped
  true — path exists: @Pending -> submit -> @Confirmed -> ship -> @Shipped

explain not reachable Order.status -> @Refunded
  false — no action produces Order.status' = @Refunded

explain terminal Order.status
  @Shipped, @Cancelled — no actions have requires status == @Shipped or @Cancelled

explain cycles Order.status
  none — all transitions are acyclic
```

### Assertions (for CI/CD)

```
assert reachable Order.status -> @Shipped          // fail if not reachable
assert not cycles Order.status                     // fail if cycles exist
assert terminal Order.status == { @Shipped, @Cancelled }  // fail if terminals don't match
```

Assertions return non-zero exit code on failure, making them suitable for CI/CD gates.

## QA Scripts

QA scripts are `.qa` files containing `load`, `ask`, `explain`, `assert`, `verify`, `simulate`, and artifact inspection statements. `verify` and `simulate` store native artifacts in the current script session; the artifact commands inspect those stored objects rather than scraping terminal output.

```
// commerce.qa
load "src/commerce/"

ask entities
ask systems

assert reachable Order.status -> @Shipped
assert reachable Order.status -> @Cancelled
assert not cycles Order.status
assert terminal Order.status == { @Shipped, @Cancelled }

explain not reachable Order.status -> @Refunded
```

Run with:

```sh
$ abide qa commerce.qa
Loaded module Commerce (3 entities, 1 system)

ask entities: Order, Customer, PaymentIntent
ask systems: Commerce, Billing

assert reachable Order.status -> @Shipped: PASS
assert reachable Order.status -> @Cancelled: PASS
assert not cycles Order.status: PASS
assert terminal Order.status == { @Shipped, @Cancelled }: PASS

explain not reachable Order.status -> @Refunded:
  false — no action produces Order.status' = @Refunded

4/4 assertions passed
```

## Artifacts In QA Scripts

`verify` runs the normal verification pipeline against the current in-memory spec and stores any evidence-bearing results as session-local artifacts. `simulate` runs one seeded forward execution and stores the resulting timeline as a native simulation artifact.

```qa
load "src/commerce/"

verify
simulate --steps 8 --seed 7 --system Commerce
artifacts
show artifact order_safety
draw artifact simulation:Commerce
state artifact simulation:Commerce 0
state artifact counterexample:order_safety 0
export artifact order_safety json
```

Artifact selectors can be:
- a numeric session ID (`1`)
- a source name (`order_safety`)
- a kind-qualified name (`counterexample:order_safety`)

Plain names resolve to the latest stored artifact with that source name in the current session. Numeric IDs remain available as low-level handles.

Artifacts are invalidated when the script changes the in-memory spec with an `abide { }` block, because the old evidence may no longer correspond to the new model.

Today, QA stores:
- evidence-bearing verification results that already emit native evidence objects: counterexamples, liveness violations, deadlocks, and admitted proof-artifact references
- native simulation runs produced by `simulate`

Scene results are still printed by `verify`, but they do not yet produce native artifacts.

## Hypothetical Scenarios

QA scripts can test "what if" scenarios using inline `abide { }` blocks that extend existing entities with new actions. The block must declare its module so the extension merges correctly:

```
// tests/refund.qa
load "src/commerce/"

abide {
  module Commerce

  entity Order {
    action refund() requires status == @Confirmed {
      status' = @Refunded
    }
  }
}

assert reachable Order.status -> @Refunded
explain path Order.status @Pending -> @Refunded
```

The `abide { }` block adds the `refund` action to the existing `Order` entity in-memory. The original spec files are not modified. This lets you explore design alternatives without changing production specs.

**Key rules:**
- `abide { }` blocks must include a `module` declaration matching the loaded specs
- Actions and fields are merged into existing entities (new actions added, existing ones preserved)
- `load` stays pure — it loads Abide files normally; duplicate entities across files are errors
- The `FlowModel` is rebuilt after each `abide { }` block

## Name Disambiguation

QA commands (`ask reachable ...`) and user function calls (`ask(x)`) are syntactically disjoint. The parser distinguishes by the second token — a QA subcommand keyword vs a parenthesis:

```
ask reachable Order.status -> @Shipped    // QA command (ask + reachable)
ask(42)                                    // user function call (ask + parenthesis)
```

If a user-defined name shadows a QA subcommand keyword, the module qualifier resolves the ambiguity: `Commerce::reachable(x)`.

## Key Design Decisions

**QA is its own language.** Not embedded Abide, not a library. Query statements (`ask`/`explain`/`assert`), load/overlay statements (`load`, `abide { }`), and verification-artifact statements (`verify`, `artifacts`, `show`, `draw`, `state`, `diff`, `export`). Simple grammar, easy to learn, easy to parse.

**Graph-based, not solver-based.** QA queries execute against a FlowModel — a precomputed graph of state transitions extracted from the IR. No SMT solver invocation. Responses are instant (microseconds). Solver-backed analysis belongs to `abide verify`.

**`explain` over `why_not`.** One keyword for both positive and negative diagnostics. `explain reachable ...` tells you why something is reachable. `explain not reachable ...` tells you why not.

**`--format json` for CI.** Machine-readable output for automated pipelines. Each result is a JSON object.

## Block-Form Queries

For power users, advanced relational queries:

```
ask {
  for e, f, s where state(e, f, s)
  not transition(e, f, from: s)
  select e, f, s
}
```

Available predicates: `state`, `transition`, `initial`, `terminal`. This is a small relational query language over the FlowModel.
