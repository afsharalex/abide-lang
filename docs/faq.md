# FAQ

### Is Abide a programming language?

No. Abide is a **specification language** — you describe what your system should do, and tools check, simulate, and verify your specifications. You don't deploy Abide as application code, but you do execute specs through the compiler and solver tooling. The output is confidence in your design, not running software.

### How does Abide compare to Alloy, TLA+, and Dafny?

Abide occupies the intersection:

- **Like Alloy:** Lightweight structural modeling with bounded exploration. Entities and types define relational structure. The solver finds counterexamples within bounds.
- **Like TLA+:** System-level temporal reasoning. Actions, events, and temporal operators (`always`, `eventually`) express system behavior over time.
- **Like Dafny:** Function and algorithm-level contracts with automated verification (planned). `requires`/`ensures` attach to functions, with loop invariants and termination measures.
- **Beyond all three:** A proof escape hatch to dependent type theory backends (Agda, Lean 4, or Rocq — under evaluation) for properties that need unbounded guarantees.

The goal is one language that scales from quick structural sketches to deep algorithmic proofs, rather than switching tools at each level.

### Can I use it today?

The language is under heavy development and will make frequent changes. The compiler currently parses and type-checks specifications — you can write entities, systems, actions, verification blocks, and scenes, and the compiler catches structural and type errors.

What's not yet connected: the Z3 solver backend (for running verification and scene checks) and proof backend integration. We will announce when an alpha release with solver support is available.

### What does the prime notation (`'`) mean?

State transitions. In an action body:
- `balance` = the current (pre-state) value
- `balance'` = the next (post-state) value

```abide
action deposit(amount: Real) {
  balance' = balance + amount    // next balance = current balance + amount
}
```

Fields not mentioned in the action body are unchanged (inertia). This is the same approach as TLA+ and Alloy.

### What does `@` mean?

State and constructor atoms. `@Pending`, `@Active`, `@USD` are named values in an enum's state space. `@OrderStatus::Paid` is a qualified atom with scope resolution.

```abide
enum Status = Active | Frozen | Closed

entity Account {
  status: Status = @Active       // default value is the Active atom

  action freeze() requires status == @Active {
    status' = @Frozen            // transition to the Frozen atom
  }
}
```

### What's the verification backend?

- **Bounded model checking:** Z3 (SMT solver). `verify` blocks will be compiled to Z3 constraints. The solver explores finite-depth event interleavings. In progress.
- **Automated unbounded checking:** For properties that are inductive or over finite state spaces, the solver will attempt to discharge them automatically without bounds. This covers many common safety properties without requiring manual proofs.
- **Manual unbounded proofs:** For properties the solver can't discharge automatically, `theorem` and `lemma` blocks export obligations to an external dependent type theory backend (Agda, Lean 4, or Rocq — under evaluation). You write the proof in the external language; Abide trusts the certificate.

### Is the language stable?

No. Abide is in active design. Syntax and semantics may change. We'll add version-tagged stability markers when the language reaches that point.

The constructs most likely to remain stable: enums, structs, type aliases, entities, actions, primed notation, `requires`/`ensures`, systems, events, `verify`/`scene` block structure, temporal operators, quantifiers.

The constructs most likely to evolve: theorem block internals, module system, trait system, algorithm verification syntax.

### What does `sorry` do?

`sorry` admits a function's entire proof obligation — postcondition, termination, everything. The function reports `ADMITTED` instead of `PROVED`, making it visually clear that the proof is incomplete. This is analogous to Lean's `sorry` or Agda's `postulate`.

```abide
fn risk_score(o: Order): Real
  ensures result >= 0.0
{
  sorry     // reports: ADMITTED fn risk_score (sorry in body, 0ms)
}
```

`todo` is similar but causes a verification error (not admission). Use `sorry` when you intend to prove later; use `todo` when the implementation is missing.

### How do I express "this should never happen"?

Use `always` with `no` or negation in a `verify` block:

```abide
verify safety for Banking[0..500] {
  // No account is ever both frozen and closed
  assert always (no a: Account |
    a.status == @Frozen and a.status == @Closed)

  // Frozen accounts never change balance
  assert always (all a: Account |
    a.status == @Frozen implies a.balance' == a.balance)
}
```

### How do I express "this should eventually happen"?

Use `eventually` in a `verify` block or construct a `scene`:

```abide
// Property: every pending order eventually gets paid or cancelled
verify liveness for Commerce[0..100] {
  assert all o: Order |
    o.status == @Pending implies
      eventually (o.status == @Paid or o.status == @Cancelled)
}

// Witness: show a specific path to payment
scene order_gets_paid for Commerce {
  given let o = one Order where o.status == @Pending and o.total == 50
  when action p = Commerce::place_order(o) { one }
  then assert o.status == @Paid
}
```
