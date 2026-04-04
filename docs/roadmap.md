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
| Temporal operators (`always`, `eventually`, `implies`) | Implemented |
| Composition operators (`->`, `&`, `\|`, `\|\|`, `^|`, `\|>`) | Implemented |
| Quantifiers (`all`, `some`, `no`, `one`, `lone`, `exists`) | Implemented |
| `theorem` and `axiom` keywords | Implemented |
| Sorry/todo stubs | Implemented |
| Compiler type-checking | Implemented |
| Module system (`module`, `include`, `pub` visibility) | Implemented |
| Z3 integration (verify, scene, theorem blocks) | Implemented |
| Tiered verification (induction, IC3/PDR, bounded fallback) | Implemented |
| Counterexample and witness traces | Implemented |
| [REPL](repl.md) (interactive specification exploration) | Implemented |
| [QA language](qa-language.md) (`ask`/`explain`/`assert`) | Implemented |
| QA scripts (`.qa` files for CI/CD) | Implemented |
| Function contracts (`requires`/`ensures`/`decreases`) | Verified |
| Imperative `fn` bodies (`var`, `while`, `if`/`else`) | Verified |
| Refinement types (`Int { $ > 0 }`, type aliases) | Verified |
| Termination measures (`decreases` for recursion and loops) | Verified |
| Call-site precondition checking (modular verification) | Verified |
| `assert`/`assume` in fn bodies (VC generation, ADMITTED diagnostic) | Verified |
| `sorry` diagnostic (ADMITTED, skips all verification) | Verified |
| Quantifiers in fn contracts (`all`/`exists` over Int/Bool/Real/Enum/Refinement) | Verified |
| Set cardinality (`#Set(...)`, `#Seq(...)`) with semantic dedup | Verified |
| Set comprehension in fn contracts (`{ x: T where P(x) }`) | Verified |
| Constructor field destructuring (Z3 ADTs, `@Ctor { field: val }`) | Verified |
| Lambda expressions in fn contracts (currying, partial application) | Verified |
| Automatic `prop` verification | Implemented |
| Circular include/use detection | Implemented |

## Next (v0.1)

| Feature | Description |
|---------|-------------|
| FSM blocks | Authoritative state transition graphs inside entities |
| `impl` blocks | Concrete type narrowing for implementation verification |
| Generic types | Parameterized types (`List[T]`, `Option[T]`) |
| Traits | Verified behavioral contracts with field bindings |

## Future (v0.2+)

| Feature | Description |
|---------|-------------|
| Proof backends | Export proof obligations to Agda, Lean 4, or Rocq |
| Simulation mode | Forward-simulate event sequences without the solver |
| Visual analyzer | Graphical state machine visualization and interactive simulation |
| Editor integration | LSP server, Tree-sitter grammar, VS Code/Neovim/Emacs plugins |
