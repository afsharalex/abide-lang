# Abide Error Reference

This page lists all error codes produced by the Abide compiler, with descriptions and examples.

## Elaboration Errors

These errors are detected during semantic analysis (after parsing).

### E001: Duplicate Declaration

Two declarations with the same name exist in the same scope.

```abide
enum Status = Active | Inactive
enum Status = Open | Closed       // error[E001]: duplicate declaration 'Status'
```

**Fix:** Rename one of the declarations, or if they are in different modules, use qualified names (`Module::Name`) to disambiguate.

---

### E002: Undefined Reference

A name was referenced that does not exist in the current scope.

```abide
entity Order {
  status: OrderState = @Pending   // error[E002]: unresolved name 'OrderState'
}
```

**Fix:** Check spelling, ensure the declaration exists, or add a `use` import if it is in another module.

---

### E003: Type Mismatch

An expression has a type that does not match what was expected.

```abide
entity Order {
  status: OrderStatus = @Pending

  action confirm() requires 42 {   // error[E003]: requires expression should be bool
    status' = @Confirmed
  }
}
```

**Fix:** Check that field types, function arguments, and operator operands have compatible types.

---

### E004: Invalid Primed Variable

A primed variable (`x'`) was used outside an action body, or on a name that is not a field.

```abide
entity Order {
  status: OrderStatus = @Pending

  action confirm() requires status == @Pending {
    unknown_field' = @Confirmed   // error[E004]: 'unknown_field' is not a field of Order
  }
}
```

**Fix:** Primed variables represent next-state values and are only valid inside action bodies and executable system command clauses. The primed name must be a declared field of the entity.

---

### E005: Cyclic Definition

A definition refers to itself (directly or transitively), creating an infinite loop.

```abide
pred is_valid(x: int) = is_valid(x)   // error[E005]: circular definition detected
```

**Fix:** Break the cycle by restructuring the definitions.

---

### E006: Invalid Scope or Visibility

A declaration was accessed from a scope where it is not available.

```abide
entity Order {
  derived total = 0
}

derived total = 0                     // error[E006]: invalid scope
```

**Fix:** Move the declaration into the scope where it is allowed.

---

### E007: Ambiguous Reference

A name resolves to multiple declarations and cannot be disambiguated.

**Fix:** Use a qualified name (`Module::Name`) to specify which declaration you mean.

---

### E008: Parameter Mismatch

The number or types of arguments do not match the declaration's parameter list.

**Fix:** Check the function or predicate signature.

---

### E009: Invalid Default Value

A field default value has an invalid type or uses an expression that is not allowed in default position.

```abide
enum Status = Active | Inactive

entity Order {
  status: Status = @Unknown          // error[E009]: Unknown is not a constructor of Status
}
```

**Fix:** Ensure the default value is a valid constructor or literal for the field's type.

---

### E010: Missing Required Field

A required field was not provided. All entity fields without defaults must be initialized.

**Fix:** Provide a value or add a default to the field declaration.

---

## Parse Errors

Parse errors are detected during syntax analysis (before semantic analysis). They show the expected syntax and what was found instead.

Common parse errors include:

- **Unexpected token:** The parser expected a specific syntax element but found something else.
- **Unexpected end of input:** The file ended before a declaration was complete (e.g., missing closing `}`).
- **Invalid keyword:** A keyword was used in the wrong context (e.g., `assert` inside a command/step body instead of a verify block).

## Verification Results

Verification is not an error — it produces results that indicate whether properties hold:

| Result | Meaning |
|--------|---------|
| **PROVED** | Property holds for all system sizes (unbounded proof via induction or IC3). |
| **CHECKED** | No counterexample found within the bounded depth. |
| **COUNTEREXAMPLE** | A trace of events was found that violates the property. |
| **PASS** | Scene scenario is satisfiable and all assertions hold. |
| **FAIL** | Scene scenario is unsatisfiable or assertions are violated. |
| **UNKNOWN** | The solver could not determine the result (timeout or unsupported expression). |
