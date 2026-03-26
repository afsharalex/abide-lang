# The QA Language

> Planned feature — not yet implemented.

QA (Query Abide) is a small, purpose-built language for querying specifications structurally. It answers questions about your spec without running the solver — what states are reachable, where are the cycles, what transitions exist, what events touch a field.

QA runs in two contexts:
- **Interactive** — via `/qa` mode in the [REPL](repl.md)
- **Scripted** — via `abide qa script.qa` for CI/CD

## Three Statement Types

| Statement | Purpose | Output |
|-----------|---------|--------|
| `ask <query>` | Query, print result | Informational |
| `explain <query>` | Query with reasoning trace | Verbose informational |
| `assert <query>` | Query, fail if false | CI/CD gate (non-zero exit) |
| `load "path"` | Load specs from file or directory | N/A (scripts only) |

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

QA scripts are `.qa` files containing `load`, `ask`, `explain`, and `assert` statements. No Abide code — specs are loaded separately.

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

## Hypothetical Scenarios

QA scripts can test "what if" scenarios by loading additional `.abide` files that extend existing modules. Each hypothetical file declares the module it extends — the module system merges them.

**Hypothetical file:**
```abide
// tests/hypotheticals/refund.abide
module Commerce

entity Order {
  action refund() requires status == @Confirmed {
    status' = @Refunded
  }
}
```

**QA script testing the hypothetical:**
```
// tests/refund.qa
load "src/commerce/"
load "tests/hypotheticals/refund.abide"

assert reachable Order.status -> @Refunded
explain path Order.status @Pending -> @Refunded
```

This lets you explore design alternatives without modifying production specs. Different scripts can load different combinations of hypotheticals.

## Key Design Decisions

**QA is its own language.** Not embedded Abide, not a library. Three statement types (`ask`/`explain`/`assert`) plus `load`. Simple grammar, easy to learn, easy to parse.

**Graph-based, not solver-based.** QA queries execute against a FlowModel — a precomputed graph of state transitions extracted from the IR. No SMT solver invocation. Responses are instant (microseconds). Solver-backed analysis belongs to `abide verify`.

**`explain` over `why_not`.** One keyword for both positive and negative diagnostics. `explain reachable ...` tells you why something is reachable. `explain not reachable ...` tells you why not.

**No Abide code in `.qa` files.** Hypotheticals live in separate `.abide` files loaded via `load`. This avoids mixed-language parsing and keeps scripts focused on queries.

## Block-Form Queries *(v0.1)*

For power users, advanced relational queries:

```
ask {
  for e, f, s where state(e, f, s)
  not transition(e, f, from: s)
  select e, f, s
}
```

Available predicates: `state`, `transition`, `initial`, `terminal`, `invariant`, `event`, `cross_call`. This is a small relational query language over the FlowModel.
