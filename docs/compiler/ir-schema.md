# Compiler JSON Schemas

Version: `v1`

This document describes the machine-readable JSON emitted by the compiler.

The compiler currently exposes two JSON surfaces:

- `abide emit-ir ...`
- `abide verify ... --report json [output_dir]`

Both are intended to be stable enough for tooling inside the Abide workspace.
When these shapes change incompatibly, bump the schema version in this file.

Fairness and stuttering defaults are recorded in
[`fairness-stuttering.md`](fairness-stuttering.md).

## 1. IR JSON

Command:

```bash
abide emit-ir path/to/spec.ab
```

Top-level shape:

```json
{
  "types": [],
  "constants": [],
  "functions": [],
  "entities": [],
  "systems": [],
  "verifies": [],
  "theorems": [],
  "axioms": [],
  "lemmas": [],
  "scenes": []
}
```

This is the serialized form of `IRProgram` from
`crates/abide/src/ir/types.rs`.

### Key IR conventions

- Sum types are encoded as tagged JSON objects.
- Most expression nodes use a `"tag"` field.
- Optional source locations appear as:

```json
{ "start": 123, "end": 145 }
```

- Assumption sets are normalized before they reach IR:
  - `stutter` is a boolean
  - `weak_fair`, `strong_fair`, and `per_tuple` are arrays of command refs

Example assumption set:

```json
{
  "stutter": true,
  "weak_fair": [
    { "system": "Billing", "command": "charge" }
  ],
  "strong_fair": [],
  "per_tuple": []
}
```

### Important top-level IR nodes

- `IRTypeEntry`
  - named type declaration after elaboration and monomorphization
- `IREntity`
  - fields, transitions, derived fields, invariants
- `IRSystem`
  - system-level fields, commands, executable actions, queries, preds, let bindings, procs
- `IRVerify`
  - bounded verification target, including store declarations and assumption set
- `IRTheorem`
  - unbounded proof target, including `by_lemmas`
- `IRScene`
  - satisfiable witness / scenario checking target

## 2. Verification Report JSON

Command:

```bash
abide verify spec.ab --report json
```

Top-level shape:

```json
{
  "kind": "verification_report",
  "version": 1,
  "files": ["/abs/path/spec.ab"],
  "summary": {
    "result_count": 1,
    "failure_count": 0,
    "diagnostic_count": 0
  }
}
```

The report includes:

- `kind`
- `version`
- `files`
- `summary`
- `config`
- `diagnostics`
- `results`

`results` is the serialized form of `Vec<VerificationResult>` from
`crates/abide/src/verify/mod.rs`.

### VerificationResult variants

- `proved`
- `checked`
- `counterexample`
- `scene_pass`
- `scene_fail`
- `unprovable`
- `fn_contract_proved`
- `fn_contract_admitted`
- `fn_contract_failed`
- `liveness_violation`
- `deadlock`

Each result object includes:

- `kind`
- `name`
- optional `span`
- optional `file`

Variant-specific fields are included only when relevant.

Behavioral detail now lives under native `evidence` payloads rather than legacy
trace-specific fields. Operational failures carry operational witness payloads;
relational failures carry relational witness payloads; proof-oriented failures
carry countermodel or proof-artifact evidence when applicable.

### TrustedAssumption

Assumptions are disclosed explicitly on results that depend on them.

Shape:

```json
{ "kind": "stutter" }
```

```json
{ "kind": "weak_fairness", "system": "Billing", "command": "charge" }
```

```json
{ "kind": "strong_fairness", "system": "Billing", "command": "charge" }
```

```json
{ "kind": "lemma", "name": "helper_lemma" }
```

```json
{ "kind": "axiom", "name": "trusted_fact" }
```

### Fairness analysis

`liveness_violation` results include `fairness_analysis`:

```json
{
  "system": "Billing",
  "command": "charge",
  "kind": "weak",
  "status": "enabled_but_starved"
}
```

`status` values:

- `enabled_and_fired`
- `enabled_but_starved`
- `never_enabled`

### Deadlock diagnostics

`deadlock` results include `event_diagnostics`:

```json
{
  "system": "Billing",
  "command": "charge",
  "reason": "guard is false"
}
```

These are explanatory diagnostics, not a proof object.

## 3. Exit-code contract

For `abide verify`:

- terminal output stays human-readable by default
- `--report json` writes the machine-readable artifact to disk
- exit code is semantic:
  - `0` if all verification targets succeed
  - non-zero if any result is a failure (`counterexample`, `scene_fail`, `unprovable`, `fn_contract_failed`, `liveness_violation`, `deadlock`)
