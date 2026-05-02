# Roadmap

Abide is in active design and implementation. This page tracks what works, what's next, and what's deferred.

Syntax and semantics are evolving. Early feedback is welcome.

## Works Now

| Feature | Status |
|---------|--------|
| Types (enums, records, ADTs, type aliases) | Implemented |
| Entities (fields, defaults, state atoms) | Implemented |
| Actions (requires/ensures, primed notation) | Implemented |
| Systems, commands, actions, and queries | Implemented |
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
| Module system (`module`, `include`, `use`) | Implemented |
| Z3 integration (verify, scene, theorem blocks) | Implemented |
| Tiered verification (induction, IC3/PDR, bounded fallback) | Implemented |
| Counterexample and witness traces | Implemented |
| Verification reports (`--report`, `--verbose`, `--debug-evidence`) | Implemented |
| [REPL](repl.md) (interactive specification exploration) | Implemented |
| [QA language](qa-language.md) (`ask`/`explain`/`assert`) | Implemented |
| QA scripts (`.qa` files for CI/CD) | Implemented |
| Native artifact inspection in REPL/QA | Implemented |
| Native simulation command (`abide simulate`) | Implemented |
| REPL/QA simulation artifact storage and exploration | Implemented |
| Function contracts (`requires`/`ensures`/`decreases`) | Verified |
| Imperative `fn` bodies (`var`, `while`, `if`/`else`) | Verified |
| Refinement types (`int { $ > 0 }`, type aliases) | Verified |
| Termination measures (`decreases` for recursion and loops) | Verified |
| Call-site precondition checking (modular verification) | Verified |
| `assert`/`assume` in fn bodies (VC generation, ADMITTED diagnostic) | Verified |
| `sorry` diagnostic (ADMITTED, skips all verification) | Verified |
| Quantifiers in fn contracts (`all`/`exists` over int/bool/real/Enum/Refinement) | Verified |
| Set cardinality (`#Set(...)`, `#Seq(...)`) with semantic dedup | Verified |
| Set comprehension in fn contracts (`{ x: T where P(x) }`) | Verified |
| Constructor field destructuring (Z3 ADTs, `@Ctor { field: val }`) | Verified |
| Lambda expressions in fn contracts (currying, partial application) | Verified |
| Automatic `prop` verification | Implemented |
| Circular include/use detection | Implemented |
| `extern`, `interface`, `implements`, `dep`, `may`, extern-boundary `saw` | Implemented on the current boundary slice |
| Proc / orchestration control-flow slice | Implemented on the current boundary slice |
| Narrow system/entity `fsm` lifecycle slice | Implemented on the current boundary slice |

## Usable With Caveats

| Area | Status |
|------|--------|
| `verify` | Usable for real bounded checking and a meaningful unbounded auto-proof fragment, but backend architecture and validation are still evolving |
| `simulate` | Usable forward executor for the current operational fragment; not an explicit-state model checker and not exhaustive bounded search |
| `extern` / `interface` / `saw` | Real compiler surface exists, but named dependency instances, richer trust disclosure, and broader boundary modeling are still deferred |
| Proc / orchestration | Real control-flow support exists; payload/dataflow and richer lifecycle semantics are still deferred |
| CVC5 backend | Experimental / partial compared to the Z3 path |

## Next (trustworthy v0.x priorities)

| Feature | Description |
|---------|-------------|
| Verification backend portfolio | Finalize backend responsibilities beyond “everything through Z3” |
| Proof manager and proof-backend boundary | Make theorem/proof routing explicit instead of ad hoc |
| Verification encoding validation | Build an oracle/mutation/CE-replay pipeline that makes the current backend trustworthy |
| CVC5 cleanup | Remove the temporary feature gate and define honest routing boundaries |
| Vertical-slice docs and examples | Keep the public docs aligned with what is actually usable now |

## Future

| Feature | Description |
|---------|-------------|
| Proof backends | Export proof obligations to Agda, Lean 4, or Rocq |
| Explicit-state model checker | Implemented on a bounded finite-state fragment; broader coverage is still widening |
| Relational/SAT backend | Implemented on a bounded routed fragment; broader coverage is still widening |
| Visual analyzer | Graphical state machine visualization and interactive simulation |
| Editor integration | LSP server, Tree-sitter grammar, VS Code/Neovim/Emacs plugins |

## What this means in practice

Today Abide is strongest on a finite or finitely scoped vertical slice:

- entity/system command-flow and state-machine specs
- bounded safety and bounded liveness checks
- scenes
- imperative helper functions with contracts
- REPL / QA / simulation-assisted exploration

The main things still outside the “trustworthy and routine” slice are:

- broader explicit-state exploration coverage
- broader relational/SAT-specialized solving coverage
- external proof backends and proof routing
- complete backend-validation coverage across all supported encodings
