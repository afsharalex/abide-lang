# Fairness And Stuttering Semantics

This note records the implementation contract for fairness and stuttering
across the current verifier surfaces.

## Assumption Defaults

| Construct | Default stutter | Fairness default |
| --- | --- | --- |
| `verify` | off | no fair commands |
| QA semantic temporal query | off | no fair commands |
| `theorem` | on | no fair commands |
| `lemma` | on | no fair commands |
| auto-verified `prop` | on | no fair commands |

`verify` blocks use no-stutter semantics by default so deadlocks remain visible.
Users opt into stuttering with `assume { stutter }`.

`theorem`, `lemma`, and auto-verified `prop` declarations use stuttering by
default because those proof obligations are interpreted over TLA-style
behaviors unless the user writes `assume { no stutter }`.

QA semantic temporal queries are lowered to synthetic `verify` blocks, not
synthetic theorems. They therefore use no-stutter defaults and report deadlocks
instead of silently accepting infinite idle behavior.

## Fairness Strength

`fair System::command` is weak fairness: if the command is continuously enabled
from some point onward, it must eventually fire.

`strong fair System::command` is strong fairness: if the command is enabled
infinitely often, it must eventually fire.

If the same command is listed as both weak and strong fair, normalization keeps
only the strong-fair obligation.

Parameterized fair commands use per-tuple fairness. The fairness obligation is
checked for each finite `(command, args)` tuple that the backend can enumerate,
not just for the command name as a whole.

## Lemma Reuse

A lemma can be used in a theorem only when the theorem's assumptions imply the
lemma's assumptions:

- A theorem with stutter enabled cannot use a lemma proven with stutter disabled.
- A theorem with stutter disabled can use a lemma proven with stutter enabled.
- A lemma requiring strong fairness requires the theorem to provide strong
  fairness for the same command.
- A lemma requiring weak fairness can be satisfied by either weak or strong
  fairness in the theorem.

## Backend Responsibilities

Backends that support temporal reasoning must preserve the effective
`AssumptionSet` from IR:

- Explicit-state checking uses the IR `stutter`, `weak_fair`, `strong_fair`, and
  `per_tuple` fields directly.
- Lasso-BMC fairness constraints use weak-vs-strong enablement and per-tuple
  expansion where finite tuple enumeration is available.
- Relational bounded verification does not currently support fair commands; it
  must decline those obligations so another backend can handle them or report a
  precise unsupported result.
- External TLC oracles must not add stronger fairness than the matching Abide
  `assume { ... }` block. When Abide uses no-stutter semantics, a TLC model may
  use an explicit real-step fairness approximation only to rule out infinite
  synthetic stuttering before the target condition is reached.

