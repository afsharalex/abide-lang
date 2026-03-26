# Roadmap

Abide is in active design and implementation. This page tracks what works, what's next, and what's deferred.

Syntax and semantics are evolving. Early feedback is welcome.

## Works Now (v0)

| Feature | Status |
|---------|--------|
| Types (enums, records, ADTs, type aliases) | Implemented |
| Entities (fields, defaults, state atoms) | Implemented |
| Actions (requires/ensures, primed notation) | Implemented |
| Systems and events | Implemented |
| Entity reference parameters (`[ref: Entity]`) | Implemented |
| Predicates (`pred`) and properties (`prop`) | Implemented |
| Pure functions (`fn ... = expr`) | Implemented |
| Constants (`const`) | Implemented |
| Match expressions (patterns, guards, or-patterns, wildcards) | Implemented |
| Verify blocks with bounds (`verify for System[0..N]`) | Syntax implemented, solver backend in progress |
| Scene blocks (given/when/then) | Syntax implemented, solver backend in progress |
| Theorem, lemma, and axiom blocks | Syntax implemented, backend not yet connected |
| Temporal operators (`always`, `eventually`, `implies`) | Implemented |
| Composition operators (`->`, `&`, `\|`, `\|\|`, `^|`, `\|>`) | Implemented |
| Quantifiers (`all`, `some`, `no`, `one`, `lone`, `exists`) | Implemented |
| `theorem` and `axiom` keywords | Implemented |
| Sorry/todo stubs | Implemented |
| Compiler type-checking | Implemented |

## Next (v0.1)

| Feature | Description |
|---------|-------------|
| FSM blocks | Authoritative state transition graphs inside entities |
| Module system | `module` declarations, `include`, `pub` visibility |
| Z3 integration | SMT solver backend for verify and scene blocks |
| Tiered verification | Automatic unbounded proofs where possible, bounded fallback |
| Trace output | Counterexample and witness traces from the solver |
| [REPL](repl.md) | Interactive specification authoring with live evaluation and mode switching |
| [QA language](qa-language.md) | Structural query language (`ask`/`explain`/`assert`) for specs |
| QA scripts | Scriptable structural checks (`.qa` files) for CI/CD |

## Future (v0.2+)

| Feature | Description |
|---------|-------------|
| Imperative `fn` bodies | `var`, `while`, `if`/`else` inside verified functions |
| Refinement types | `Int{I64 \| $ > 0}` — types with embedded constraints |
| `impl` blocks | Concrete type narrowing for implementation verification |
| Termination measures | `decreases` clauses for recursive functions and loops |
| Generic types | Parameterized types (`List[T]`, `Option[T]`) |
| Traits | Verified behavioral contracts with field bindings |
| Proof backends | Export proof obligations to Agda, Lean 4, or Rocq |
| Simulation mode | Forward-simulate event sequences without the solver |
| Visual analyzer | Graphical state machine visualization, transition exploration, and interactive simulation |
| nREPL server | Editor integration for VS Code, Emacs, Neovim via REPL server mode |
