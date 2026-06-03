# Editor Integration

Abide's language server gives editors fast feedback while keeping full
verification under the CLI and REPL. Editor diagnostics are meant for the
current buffer and must never replace the verification result that `abide
verify` or the REPL reports before running a `verify` block.

## Verification Scope

The LSP may check function-local obligations for quick feedback:

- `ensures` obligations for a function body
- `requires` obligations at function call sites
- `decreases` obligations for recursive functions
- refinement-type obligations that lower to function preconditions

The LSP also has a focused proof-obligation path for explicit theorem or lemma
preflight. That path reports selected theorem/lemma results and admissions, but
it does not dispatch `verify` blocks, scenes, props, or unrelated function
checks. Expensive proof search such as IC3/PDR remains gated by explicit
verification configuration and is not part of ordinary edit-time feedback.

`verify` and `scene` blocks still run through the CLI or REPL. Before those
blocks run, Abide verifies function contracts for the loaded program. A hard
function verification failure blocks later verification. A scoped `sorry` or
`todo` inside one function admits that function's body obligation only; it does
not disable verification for other functions. Trusted theorem admissions, such
as an external proof artifact reference, surface as admitted diagnostics/status
so the editor can disclose the trust boundary without treating the proof as a
solver failure.

## Trigger Policy

Editors can choose how aggressively function verification runs by passing LSP
initialization options:

```json
{
  "abide": {
    "verification": {
      "mode": "change",
      "debounceMs": 300,
      "timeoutMs": 1500
    }
  }
}
```

Supported modes:

| Mode | Behavior |
|------|----------|
| `change` | Verify after text changes, using the debounce window. This is the default. |
| `save` | Verify only when the document is saved. |
| `manual` | Do not schedule verification automatically; the editor may expose an explicit command. |
| `disabled` | Do not run editor verification. |

Editors may also set `"enabled": false` as a shorthand for disabled mode. The
same options may be passed under either `abide.verification` or
`verification`.

## Freshness And Timeouts

Every editor verification request is tied to the root file, the document
version, and an internal generation number. If a newer edit or newer request
arrives first, the older result is treated as stale and is not published. This
prevents slow checks from overwriting diagnostics for newer source text.

Long-running checks should use the configured `timeoutMs` value. Timeout and
cancellation outcomes are reported as typed editor-verification statuses rather
than as ordinary language errors.

## Status Codes

Editor verification statuses use stable codes so clients can render them as
status messages, progress items, or diagnostics:

| Code | Meaning |
|------|---------|
| `abide.lsp.verification.verifying` | Verification is running. |
| `abide.lsp.verification.verified` | Verification completed without failures. |
| `abide.lsp.verification.failed` | One or more obligations failed. |
| `abide.lsp.verification.admitted` | One or more `sorry`, `todo`, or `assume` obligations were admitted. |
| `abide.lsp.verification.disabled` | Editor verification is disabled. |
| `abide.lsp.verification.timeout` | Verification exceeded the configured timeout. |
| `abide.lsp.verification.cancelled` | Verification was cancelled by a newer request or client action. |
| `abide.lsp.verification.stale` | A completed result was for an older document version. |
