//! Entity collection — entities, fields, actions, FSMs, derived fields, cycle detection.

use std::collections::{HashMap, HashSet};

use super::expr::{collect_expr, parse_float_text};
use super::{resolve_param_ty, resolve_type_ref};
use crate::ast;
use crate::elab::env::Env;
use crate::elab::error::{ElabError, ErrorKind};
use crate::elab::types::{
    BinOp, BuiltinTy, EAction, EDerived, EEntity, EExpr, EField, EFieldDefault, EFsm, EFsmRow,
    EInvariant, EPattern, Literal, Ty,
};

// ── Entity declarations ──────────────────────────────────────────────

pub(super) fn collect_entity(env: &mut Env, ed: &ast::EntityDecl) {
    let name = &ed.name;
    let mut fields = Vec::new();
    let mut actions = Vec::new();
    let mut derived_fields = Vec::new();
    let mut invariants = Vec::new();
    // collect raw fsm declarations now; validate
    // them after fields are known so we can resolve the field name to
    // its enum type.
    let mut raw_fsms: Vec<&ast::FsmDecl> = Vec::new();
    for item in &ed.items {
        match item {
            ast::EntityItem::Field(f) => fields.push(collect_field(f)),
            ast::EntityItem::Action(a) => actions.push(collect_action(a)),
            // derived field declarations on the
            // entity. Body type is inferred from the expression.
            ast::EntityItem::Derived(d) => derived_fields.push(collect_derived(d)),
            // invariant declarations on the
            // entity. Body is elaborated as a Boolean expression.
            ast::EntityItem::Invariant(inv) => invariants.push(collect_invariant(inv)),
            // defer fsm validation until fields are
            // collected so we can resolve the field name and enum type.
            ast::EntityItem::Fsm(fsm) => raw_fsms.push(fsm),
            ast::EntityItem::Error(_) => {}
        }
    }

    // validate and collect fsm declarations.
    let fsm_decls = collect_fsms(env, name, &fields, &raw_fsms, ed.span);

    // for each fsm, synthesize the
    // `is_terminal` (or `<field>_is_terminal` for multi-fsm entities)
    // derived field. The synthesis is suppressed if the user has
    // already declared a derived field with the same name. Synthesized
    // fields are added to `derived_fields` before the duplicate-name
    // check below so they participate in uniqueness enforcement.
    synthesize_fsm_is_terminal(env, &fsm_decls, &mut derived_fields);

    // structural reachability check at declaration
    // time. For each fsm, walk the transition graph from the field's
    // initial state and emit a warning for any variant that appears in
    // the fsm rows but is not reachable. This is a warning, not an
    // error — explicitly allows non-terminating monitor
    // states; the warning is meant to catch typos and dead branches.
    for fsm in &fsm_decls {
        check_fsm_reachability(env, name, fsm);
    }

    // reject any action body that contains
    // a primed assignment nested inside an `if`/`while`/`match`/block.
    // The IR lowering's `extract_updates` only walks top-level
    // `Assign(Prime, _)` nodes, so nested primes would silently
    // disappear from `IRTransition::updates` — bypassing the fsm
    // validity check and silently dropping the mutation. We close
    // this gap at elab time so the user gets a clear diagnostic
    // instead of unsound verification.
    check_action_bodies_no_nested_primes(env, name, &actions);

    // static violation check. For each fsm, scan
    // every entity action that prime-assigns the fsm field. If the
    // (source, target) pair extracted from the action's `requires` +
    // body literals is not in the transition table, emit an elab
    // error with the failing pair, the action name, and valid
    // alternatives. Non-literal actions are skipped — they fall
    // through to the verifier's per-action constraint as a backstop.
    check_fsm_action_violations(env, name, &actions, &fsm_decls);

    // enforce
    // name uniqueness across fields, derived fields, actions, AND
    // invariants. / both require unique names within
    // the entity body. The check runs before the cycle detector so
    // duplicate names are reported even when their bodies would cycle.
    let mut seen: HashSet<String> = HashSet::new();
    for f in &fields {
        seen.insert(f.name.clone());
    }
    for a in &actions {
        if !seen.insert(a.name.clone()) {
            env.errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!(
                    "duplicate name `{}` in entity `{}` — conflicts with \
                     an earlier field, derived field, invariant, or action declaration",
                    a.name, name
                ),
                String::new(),
                a.span.unwrap_or(ed.span),
            ));
        }
    }
    for d in &derived_fields {
        if !seen.insert(d.name.clone()) {
            env.errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!(
                    "duplicate name `{}` for derived field in entity `{}` \
                     — conflicts with an earlier field, derived field, \
                     invariant, or action declaration",
                    d.name, name
                ),
                String::new(),
                d.span.unwrap_or(ed.span),
            ));
        }
    }
    for inv in &invariants {
        if !seen.insert(inv.name.clone()) {
            env.errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!(
                    "duplicate name `{}` for invariant in entity `{}` \
                     — conflicts with an earlier field, derived field, \
                     invariant, or action declaration",
                    inv.name, name
                ),
                String::new(),
                inv.span.unwrap_or(ed.span),
            ));
        }
    }

    // detect cycles in derived field references
    // before the entity is committed to the environment.
    if let Some(cycle) = detect_derived_cycle(&derived_fields) {
        env.errors.push(ElabError::with_span(
            ErrorKind::CyclicDefinition,
            crate::messages::derived_cycle(&cycle),
            String::new(),
            ed.span,
        ));
    }

    let ee = EEntity {
        name: name.clone(),
        fields,
        actions,
        derived_fields,
        invariants,
        fsm_decls,
        span: Some(ed.span),
    };
    let info = env.make_decl_info(
        crate::elab::env::DeclKind::Entity,
        name.clone(),
        None,
        ed.visibility,
        ed.span,
    );
    env.add_decl(name, info);
    env.insert_entity(name, ee);
}

/// collect a `derived NAME = EXPR` declaration
/// into its elab form. The body is run through `collect_expr` and the
/// derived field's type is inferred from `body.ty()` ( says
/// the type is inferred from the body).
pub(super) fn collect_derived(d: &ast::DerivedDecl) -> EDerived {
    let body = collect_expr(&d.body);
    let ty = body.ty();
    EDerived {
        name: d.name.clone(),
        body,
        ty,
        span: Some(d.span),
    }
}

/// collect an `invariant NAME { EXPR }`
/// declaration into its elab form. The body is run through
/// `collect_expr`. Type-checking that the body is Boolean is left to
/// later passes (the verifier will reject non-Bool encodings at
/// `encode_property_at_step` time).
pub(super) fn collect_invariant(inv: &ast::InvariantDecl) -> EInvariant {
    let body = collect_expr(&inv.body);
    EInvariant {
        name: inv.name.clone(),
        body,
        span: Some(inv.span),
    }
}

/// validate and collect every `fsm` declaration on
/// an entity. The validation:
/// 1. Each fsm references a field that exists on the entity ().
/// 2. The field's static type is an enum ().
/// 3. Every atom in the transition rows is a variant of that enum.
/// 4. At most one fsm per field ( — multiple fsms per entity
///    are legal but each must target a distinct field).
///
/// Errors are pushed to `env.errors`; the returned vector contains
/// only the fsms that fully validated. The reachability check (Item
/// 50.5) runs as a separate pass after this collection.
pub(super) fn collect_fsms(
    env: &mut Env,
    entity_name: &str,
    fields: &[EField],
    raw_fsms: &[&ast::FsmDecl],
    _entity_span: crate::span::Span,
) -> Vec<EFsm> {
    let mut result: Vec<EFsm> = Vec::new();
    let mut seen_fields: HashSet<String> = HashSet::new();

    for raw in raw_fsms {
        // at most one fsm per field.
        if !seen_fields.insert(raw.field.clone()) {
            env.errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                crate::messages::fsm_duplicate(entity_name, &raw.field),
                String::new(),
                raw.span,
            ));
            continue;
        }

        // the field must exist on the entity.
        let Some(field) = fields.iter().find(|f| f.name == raw.field) else {
            env.errors.push(ElabError::with_span(
                ErrorKind::UndefinedRef,
                crate::messages::fsm_unknown_field(entity_name, &raw.field),
                String::new(),
                raw.span,
            ));
            continue;
        };

        // the field's type must be an enum.
        let Some((enum_name, variants)) = resolve_to_enum(&field.ty, env) else {
            env.errors.push(ElabError::with_span(
                ErrorKind::TypeMismatch,
                crate::messages::fsm_field_not_enum(entity_name, &raw.field),
                String::new(),
                raw.span,
            ));
            continue;
        };
        let enum_name = enum_name.to_owned();
        let variants: Vec<String> = variants.to_vec();

        // Validate each row's atoms against the variant list. We
        // collect rows that fully validate; rows with bad atoms are
        // dropped from the EFsm but the diagnostic is still emitted.
        let mut rows: Vec<EFsmRow> = Vec::new();
        let mut row_had_error = false;
        for row in &raw.rows {
            if !variants.contains(&row.from) {
                env.errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    crate::messages::fsm_unknown_variant(
                        entity_name,
                        &raw.field,
                        &row.from,
                        &enum_name,
                    ),
                    String::new(),
                    row.span,
                ));
                row_had_error = true;
                continue;
            }
            let mut tgt_ok = true;
            for tgt in &row.targets {
                if !variants.contains(tgt) {
                    env.errors.push(ElabError::with_span(
                        ErrorKind::UndefinedRef,
                        crate::messages::fsm_unknown_variant(
                            entity_name,
                            &raw.field,
                            tgt,
                            &enum_name,
                        ),
                        String::new(),
                        row.span,
                    ));
                    tgt_ok = false;
                    row_had_error = true;
                }
            }
            if tgt_ok {
                rows.push(EFsmRow {
                    from: row.from.clone(),
                    targets: row.targets.clone(),
                    span: Some(row.span),
                });
            }
        }
        // If any row was malformed we skip the whole fsm; partial
        // tables would produce confusing downstream behavior.
        if row_had_error {
            continue;
        }

        result.push(EFsm {
            field: raw.field.clone(),
            enum_name,
            rows,
            initial: field_initial_state(field),
            span: Some(raw.span),
        });
    }

    result
}

/// Resolve a type to an enum, following named lookups in
/// `env.types` and unwrapping `Alias` indirections. Returns the enum
/// name and its variant list, or `None` if the type is not an enum.
///
/// At collect time the `env.types` map is keyed by module-qualified
/// names (e.g. `T::OrderStatus`), so the qualified form is tried
/// first. After `build_working_namespace` runs the keys are flattened
/// to bare names, so the bare lookup is the fallback path.
pub(super) fn resolve_to_enum<'a>(ty: &'a Ty, env: &'a Env) -> Option<(&'a str, &'a [String])> {
    match ty {
        Ty::Enum(name, variants) => Some((name.as_str(), variants.as_slice())),
        Ty::Named(name) => {
            let qualified = match &env.module_name {
                Some(m) => format!("{m}::{name}"),
                None => name.clone(),
            };
            env.types
                .get(&qualified)
                .or_else(|| env.types.get(name.as_str()))
                .and_then(|t| resolve_to_enum(t, env))
        }
        Ty::Alias(_, inner) => resolve_to_enum(inner, env),
        _ => None,
    }
}

/// Extract the initial state of an fsm field from the field's default
/// value. The user typically writes `status: OrderStatus = @cart`,
/// which collects to `EFieldDefault::Value(EExpr::Var(_, "cart", _))`
/// or `EExpr::Qual(_, "OrderStatus", "cart", _)`. Returns the bare
/// variant name in either case, or `None` if the default is missing
/// or non-literal (e.g., `in {a, b}` or `where pred`).
pub(super) fn field_initial_state(field: &EField) -> Option<String> {
    match &field.default {
        Some(EFieldDefault::Value(EExpr::Var(_, name, _))) => Some(name.clone()),
        Some(EFieldDefault::Value(EExpr::Qual(_, _, name, _))) => Some(name.clone()),
        _ => None,
    }
}

/// Look up an enum's variant list from the env. Tries the
/// module-qualified key first (collect-time path) then the bare key
/// (post-`build_working_namespace` path).
pub(super) fn env_enum_variants<'a>(env: &'a Env, enum_name: &str) -> Option<&'a [String]> {
    let qualified = match &env.module_name {
        Some(m) => format!("{m}::{enum_name}"),
        None => enum_name.to_owned(),
    };
    let ty = env
        .types
        .get(&qualified)
        .or_else(|| env.types.get(enum_name))?;
    if let Ty::Enum(_, variants) = ty {
        Some(variants.as_slice())
    } else {
        None
    }
}

/// structural reachability checks at declaration
/// time. Two complementary passes that emit warnings (not errors)
/// because explicitly allows non-terminating monitor states:
///
/// 1. **Forward (reachable from initial).** BFS from the field's
///    initial state and warn for every variant mentioned in the fsm
///    rows but not visited. Catches typos and orphaned branches.
///    Skipped if the field has no statically-determinable initial
///    value (e.g. `status: S in {a, b}`).
///
/// 2. **Backward ("can reach a terminal").** For every non-terminal
///    state, walk forward to see whether any terminal is reachable.
///    If not, the state is a trap (sink loop or dead-end with no
///    exit) — emit a warning. This is the spec wording:
///    "every non-terminal state must have a path to at least one
///    terminal state in the fsm graph."
///
/// Variants declared in the enum but never mentioned in the fsm rows
/// are deliberately NOT flagged — they may belong to other state
/// machines or be intentionally out-of-fsm-scope.
pub(super) fn check_fsm_reachability(env: &mut Env, entity_name: &str, fsm: &EFsm) {
    use crate::elab::error::Severity;

    // Adjacency list keyed by source state, plus the set of every
    // variant mentioned anywhere in the rows.
    let mut adj: HashMap<String, Vec<String>> = HashMap::new();
    let mut mentioned: HashSet<String> = HashSet::new();
    for row in &fsm.rows {
        mentioned.insert(row.from.clone());
        for tgt in &row.targets {
            mentioned.insert(tgt.clone());
        }
        adj.entry(row.from.clone())
            .or_default()
            .extend(row.targets.iter().cloned());
    }

    // Terminal set: variants for which no row declares an outgoing
    // transition. Matches the synthesized-`is_terminal` set.
    let terminals: HashSet<String> = mentioned
        .iter()
        .filter(|v| {
            !fsm.rows
                .iter()
                .any(|r| r.from == **v && !r.targets.is_empty())
        })
        .cloned()
        .collect();

    // ── Forward pass: BFS from initial ──────────────────────────────
    if let Some(initial) = fsm.initial.clone() {
        let mut reachable: HashSet<String> = HashSet::new();
        let mut frontier: Vec<String> = vec![initial];
        while let Some(state) = frontier.pop() {
            if reachable.insert(state.clone()) {
                if let Some(neighbors) = adj.get(&state) {
                    for n in neighbors {
                        if !reachable.contains(n) {
                            frontier.push(n.clone());
                        }
                    }
                }
            }
        }

        let mut unreachable: Vec<&String> = mentioned
            .iter()
            .filter(|v| !reachable.contains(*v))
            .collect();
        unreachable.sort();
        for state in unreachable {
            let mut warn = ElabError::with_span(
                ErrorKind::UndefinedRef,
                crate::messages::fsm_unreachable_state(entity_name, &fsm.field, state),
                String::new(),
                fsm.span.unwrap_or(crate::span::Span { start: 0, end: 0 }),
            );
            warn.severity = Severity::Warning;
            env.errors.push(warn);
        }
    }

    // ── Backward pass: every non-terminal can reach a terminal ──────
    // Compute the set of states from which some terminal is reachable
    // by repeatedly relaxing along forward edges. Start with the
    // terminal set and grow until fixed point. Equivalent to reverse
    // BFS from terminals but uses the existing adjacency list.
    let mut can_reach_terminal: HashSet<String> = terminals.clone();
    let mut changed = true;
    while changed {
        changed = false;
        for state in &mentioned {
            if can_reach_terminal.contains(state) {
                continue;
            }
            if let Some(neighbors) = adj.get(state) {
                if neighbors.iter().any(|n| can_reach_terminal.contains(n)) {
                    can_reach_terminal.insert(state.clone());
                    changed = true;
                }
            }
        }
    }

    let mut trapped: Vec<&String> = mentioned
        .iter()
        .filter(|v| !terminals.contains(*v) && !can_reach_terminal.contains(*v))
        .collect();
    trapped.sort();
    for state in trapped {
        let mut warn = ElabError::with_span(
            ErrorKind::UndefinedRef,
            crate::messages::fsm_trap_state(entity_name, &fsm.field, state),
            String::new(),
            fsm.span.unwrap_or(crate::span::Span { start: 0, end: 0 }),
        );
        warn.severity = Severity::Warning;
        env.errors.push(warn);
    }
}

/// walk every entity action body and
/// reject any `Prime` expression that is not the LHS of a top-level
/// `Assign` statement. The IR lowering's `extract_updates` only sees
/// top-level `Assign(Prime, _)` nodes, so a nested prime like
/// `if cond { status' = @done }` would silently disappear from the
/// `IRTransition::updates` list. The verifier would then frame the
/// field as unchanged — bypassing both the fsm validity check and
/// any user assertion that depends on the mutation.
///
/// Closing the gap at elab time means users get a clear diagnostic
/// pointing at the offending prime, instead of unsound verification.
/// The recommended refactor is to split the action into multiple
/// guarded actions:
/// action set_done() requires cond { status' = @done }
/// action set_pending() requires !cond { status' = @pending }
pub(super) fn check_action_bodies_no_nested_primes(
    env: &mut Env,
    entity_name: &str,
    actions: &[EAction],
) {
    for action in actions {
        for stmt in &action.body {
            // A statement is well-formed if it is itself a top-level
            // `Assign(Prime, rhs)` and the RHS contains no further
            // primes. Otherwise we walk the whole expression and
            // report any prime we find.
            if let EExpr::Assign(_, lhs, rhs, _) = stmt {
                if matches!(lhs.as_ref(), EExpr::Prime(_, _, _)) {
                    if let Some(span) = find_first_prime(rhs) {
                        push_nested_prime_error(env, entity_name, &action.name, span);
                    }
                    continue;
                }
            }
            if let Some(span) = find_first_prime(stmt) {
                push_nested_prime_error(env, entity_name, &action.name, span);
            }
        }
    }
}

/// Push the standardized "nested prime" diagnostic for a single
/// offending span.
pub(super) fn push_nested_prime_error(
    env: &mut Env,
    entity_name: &str,
    action_name: &str,
    span: crate::span::Span,
) {
    env.errors.push(ElabError::with_span(
        ErrorKind::InvalidPrime,
        format!(
            "{}: nested prime in `{entity_name}::{action_name}`",
            crate::messages::ACTION_NESTED_PRIME
        ),
        String::new(),
        span,
    ));
}

/// Walk an `EExpr` and return the span of the first `Prime`
/// subexpression encountered, if any. Visits every variant exhaustively
/// so new EExpr forms can't accidentally hide nested primes from the
/// check.
pub(super) fn find_first_prime(expr: &EExpr) -> Option<crate::span::Span> {
    match expr {
        EExpr::Prime(_, _, span) => Some(span.unwrap_or(crate::span::Span { start: 0, end: 0 })),
        EExpr::Lit(_, _, _)
        | EExpr::Var(_, _, _)
        | EExpr::Qual(_, _, _, _)
        | EExpr::Unresolved(_, _)
        | EExpr::Sorry(_)
        | EExpr::Todo(_) => None,
        EExpr::Field(_, e, _, _)
        | EExpr::UnOp(_, _, e, _)
        | EExpr::Always(_, e, _)
        | EExpr::Eventually(_, e, _)
        | EExpr::Historically(_, e, _)
        | EExpr::Once(_, e, _)
        | EExpr::Previously(_, e, _)
        | EExpr::Assert(_, e, _)
        | EExpr::Assume(_, e, _)
        | EExpr::Card(_, e, _) => find_first_prime(e),
        EExpr::BinOp(_, _, a, b, _)
        | EExpr::Until(_, a, b, _)
        | EExpr::Since(_, a, b, _)
        | EExpr::Seq(_, a, b, _)
        | EExpr::SameStep(_, a, b, _)
        | EExpr::In(_, a, b, _)
        | EExpr::Pipe(_, a, b, _)
        | EExpr::Index(_, a, b, _)
        | EExpr::Assign(_, a, b, _) => find_first_prime(a).or_else(|| find_first_prime(b)),
        EExpr::Call(_, callee, args, _) => {
            find_first_prime(callee).or_else(|| args.iter().find_map(find_first_prime))
        }
        EExpr::CallR(_, callee, refs, args, _) => find_first_prime(callee)
            .or_else(|| refs.iter().find_map(find_first_prime))
            .or_else(|| args.iter().find_map(find_first_prime)),
        EExpr::Quant(_, _, _, _, body, _) => find_first_prime(body),
        EExpr::Choose(_, _, _, predicate, _) => {
            predicate.as_ref().and_then(|pred| find_first_prime(pred))
        }
        EExpr::Let(bindings, body, _) => bindings
            .iter()
            .find_map(|(_, _, rhs)| find_first_prime(rhs))
            .or_else(|| find_first_prime(body)),
        EExpr::Lam(_, _, body, _) => find_first_prime(body),
        EExpr::NamedPair(_, _, e, _) => find_first_prime(e),
        EExpr::TupleLit(_, items, _) | EExpr::SetLit(_, items, _) | EExpr::SeqLit(_, items, _) => {
            items.iter().find_map(find_first_prime)
        }
        EExpr::MapLit(_, kvs, _) => kvs
            .iter()
            .find_map(|(k, v)| find_first_prime(k).or_else(|| find_first_prime(v))),
        EExpr::Match(scrut, arms, _) => find_first_prime(scrut).or_else(|| {
            arms.iter().find_map(|(_, guard, body)| {
                guard
                    .as_ref()
                    .and_then(find_first_prime)
                    .or_else(|| find_first_prime(body))
            })
        }),
        EExpr::MapUpdate(_, m, k, v, _) => find_first_prime(m)
            .or_else(|| find_first_prime(k))
            .or_else(|| find_first_prime(v)),
        EExpr::SetComp(_, projection, _, _, source, filter, _) => projection
            .as_ref()
            .and_then(|p| find_first_prime(p))
            .or_else(|| source.as_deref().and_then(find_first_prime))
            .or_else(|| find_first_prime(filter)),
        EExpr::RelComp(_, projection, bindings, filter, _) => find_first_prime(projection)
            .or_else(|| {
                bindings
                    .iter()
                    .filter_map(|binding| binding.source.as_deref())
                    .find_map(find_first_prime)
            })
            .or_else(|| find_first_prime(filter)),
        EExpr::QualCall(_, _, _, args, _) => args.iter().find_map(find_first_prime),
        // Imperative constructs — these are exactly the forms that
        // hide nested primes from `extract_updates`. Walk into every
        // sub-expression so the rejection bites.
        EExpr::Block(stmts, _) => stmts.iter().find_map(find_first_prime),
        EExpr::VarDecl(_, _, init, rest, _) => {
            find_first_prime(init).or_else(|| find_first_prime(rest))
        }
        EExpr::While(cond, _, body, _) => find_first_prime(cond).or_else(|| find_first_prime(body)),
        EExpr::IfElse(cond, then_e, else_e, _) => find_first_prime(cond)
            .or_else(|| find_first_prime(then_e))
            .or_else(|| else_e.as_ref().and_then(|e| find_first_prime(e))),
        EExpr::Saw(_, _, _, args, _) => args
            .iter()
            .filter_map(|a| a.as_ref())
            .find_map(|e| find_first_prime(e)),
        EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => {
            fields.iter().find_map(|(_, e)| find_first_prime(e))
        }
        EExpr::Aggregate(_, _, _, _, body, in_filter, _) => {
            find_first_prime(body).or_else(|| in_filter.as_ref().and_then(|f| find_first_prime(f)))
        }
    }
}

/// static fsm violation check. For each fsm,
/// walk every entity action and look for prime assignments to the fsm
/// field. If the action's `requires` and the assignment's RHS are
/// both literal atoms (the common case for state-machine transitions
/// like `requires status == @cart { status' = @placed }`), check the
/// (source, target) pair against the transition table; emit an elab
/// error if missing.
///
/// Non-literal actions (dynamic update values, complex requires,
/// missing requires) are skipped — the verifier's per-action
/// constraint in `encode_action` is the backstop for those.
pub(super) fn check_fsm_action_violations(
    env: &mut Env,
    entity_name: &str,
    actions: &[EAction],
    fsm_decls: &[EFsm],
) {
    for fsm in fsm_decls {
        // Build a fast (from, to) lookup from the table.
        let allowed: HashSet<(String, String)> = fsm
            .rows
            .iter()
            .flat_map(|r| {
                let from = r.from.clone();
                r.targets.iter().map(move |t| (from.clone(), t.clone()))
            })
            .collect();

        for action in actions {
            let assignments = collect_prime_assignments(&action.body, &fsm.field);
            for (target_atom, span) in assignments {
                let sources = literal_sources_from_requires(&action.requires, &fsm.field);
                if sources.is_empty() {
                    continue; // unconstrained source — defer to verifier
                }
                for source in sources {
                    if !allowed.contains(&(source.clone(), target_atom.clone())) {
                        let valid: Vec<String> = fsm
                            .rows
                            .iter()
                            .filter(|r| r.from == source)
                            .flat_map(|r| r.targets.iter().cloned())
                            .collect();
                        env.errors.push(ElabError::with_span(
                            ErrorKind::TypeMismatch,
                            crate::messages::fsm_action_violation(
                                entity_name,
                                &fsm.field,
                                &action.name,
                                &source,
                                &target_atom,
                                &valid,
                            ),
                            String::new(),
                            span.or(action.span)
                                .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    }
                }
            }
            // Suppress unused-import warnings on `EAction` if it isn't
            // referenced anywhere else in this scope.
            let _ = std::marker::PhantomData::<EAction>;
        }
    }
}

/// Find every prime-assignment in `body` whose LHS is `field'`. Each
/// hit is returned as `(target_atom_name, span)` where `target_atom`
/// is extracted by `literal_atom`. Non-literal RHS expressions are
/// skipped (the elab check can't reason about them statically).
pub(super) fn collect_prime_assignments(
    body: &[EExpr],
    field: &str,
) -> Vec<(String, Option<crate::span::Span>)> {
    let mut out = Vec::new();
    for expr in body {
        collect_prime_assignments_inner(expr, field, &mut out);
    }
    out
}

pub(super) fn collect_prime_assignments_inner(
    expr: &EExpr,
    field: &str,
    out: &mut Vec<(String, Option<crate::span::Span>)>,
) {
    if let EExpr::Assign(_, lhs, rhs, span) = expr {
        if let EExpr::Prime(_, inner, _) = lhs.as_ref() {
            if let EExpr::Var(_, name, _) = inner.as_ref() {
                if name == field {
                    if let Some(atom) = literal_atom(rhs) {
                        out.push((atom, *span));
                    }
                }
            }
        }
    }
}

/// Extract the bare variant name from an `EExpr` that's a literal
/// state-atom expression. Both single-component (`@cart`) and
/// qualified (`@OrderStatus::cart`) forms are handled.
pub(super) fn literal_atom(expr: &EExpr) -> Option<String> {
    match expr {
        EExpr::Var(_, name, _) | EExpr::Qual(_, _, name, _) => Some(name.clone()),
        _ => None,
    }
}

/// Walk a list of `requires` expressions and return every literal
/// source value that constrains the named field. Handles the common
/// pattern `field == @atom` (and the symmetric form), `field == @a ||
/// field == @b`, and conjunctions like `field == @a AND other`.
/// Anything more complex is treated as "unconstrained" and the empty
/// vec is returned for that requires.
pub(super) fn literal_sources_from_requires(requires: &[EExpr], field: &str) -> Vec<String> {
    let mut sources: Vec<String> = Vec::new();
    for req in requires {
        extract_source_atoms(req, field, &mut sources);
    }
    sources
}

pub(super) fn extract_source_atoms(expr: &EExpr, field: &str, out: &mut Vec<String>) {
    match expr {
        EExpr::BinOp(_, BinOp::Eq, lhs, rhs, _) => {
            // `field == @atom` or `@atom == field`
            if matches!(lhs.as_ref(), EExpr::Var(_, n, _) if n == field) {
                if let Some(atom) = literal_atom(rhs) {
                    out.push(atom);
                }
            }
            if matches!(rhs.as_ref(), EExpr::Var(_, n, _) if n == field) {
                if let Some(atom) = literal_atom(lhs) {
                    out.push(atom);
                }
            }
        }
        EExpr::BinOp(_, BinOp::Or, lhs, rhs, _) => {
            extract_source_atoms(lhs, field, out);
            extract_source_atoms(rhs, field, out);
        }
        EExpr::BinOp(_, BinOp::And, lhs, rhs, _) => {
            // Either side may carry the source constraint. We collect
            // both — at most one will match the field, and the other
            // contributes nothing.
            extract_source_atoms(lhs, field, out);
            extract_source_atoms(rhs, field, out);
        }
        _ => {}
    }
}

/// synthesize the `is_terminal` derived field
/// for each fsm on the entity, unless the user has already defined a
/// derived field with the same name (user override per ).
///
/// Single-fsm entities get a `is_terminal` field; multi-fsm entities
/// get one `<field>_is_terminal` per fsm (so the names don't collide).
/// The synthesized body is `field == @t1 || field == @t2 ||...` over
/// the inferred terminal set (variants with no outgoing transitions).
pub(super) fn synthesize_fsm_is_terminal(
    env: &Env,
    fsm_decls: &[EFsm],
    derived_fields: &mut Vec<EDerived>,
) {
    let multi_fsm = fsm_decls.len() > 1;
    for fsm in fsm_decls {
        let Some(variants) = env_enum_variants(env, &fsm.enum_name) else {
            continue;
        };
        // Inferred terminal set: variants for which no row declares an
        // outgoing transition (whether or not they appear as a `from`
        // with empty targets).
        let terminals: Vec<String> = variants
            .iter()
            .filter(|v| {
                !fsm.rows
                    .iter()
                    .any(|r| r.from == **v && !r.targets.is_empty())
            })
            .cloned()
            .collect();
        if terminals.is_empty() {
            // Pathological fsm with no terminal states (every variant
            // has outgoing edges). would also flag this via
            // the reachability check; here we just skip synthesis so
            // we don't emit a `is_terminal = false` derived field.
            continue;
        }

        let synth_name = if multi_fsm {
            format!("{}_is_terminal", fsm.field)
        } else {
            "is_terminal".to_owned()
        };

        // user override wins, no warning.
        if derived_fields.iter().any(|d| d.name == synth_name) {
            continue;
        }

        // Build the body in the AST domain so we can hand it to the
        // existing `collect_derived` pipeline. The body is
        // `field == @t1 || field == @t2 ||...` using
        // `State2(enum_name, variant)` for each terminal so the atom
        // is unambiguous w.r.t. variant-name collisions across enums.
        let span = fsm.span.unwrap_or(crate::span::Span { start: 0, end: 0 });
        let field_var_ast = ast::Expr {
            kind: ast::ExprKind::Var(fsm.field.clone()),
            span,
        };
        let mut disjuncts: Vec<ast::Expr> = Vec::new();
        for term in &terminals {
            let atom = ast::Expr {
                kind: ast::ExprKind::State2(fsm.enum_name.clone(), term.clone()),
                span,
            };
            let eq = ast::Expr {
                kind: ast::ExprKind::Eq(Box::new(field_var_ast.clone()), Box::new(atom)),
                span,
            };
            disjuncts.push(eq);
        }
        let body = disjuncts
            .into_iter()
            .reduce(|a, b| ast::Expr {
                kind: ast::ExprKind::Or(Box::new(a), Box::new(b)),
                span,
            })
            .expect("non-empty terminals checked above");

        let derived_ast = ast::DerivedDecl {
            name: synth_name,
            body,
            span,
        };
        derived_fields.push(collect_derived(&derived_ast));
        // Note: env is &Env so we cannot push to env.errors here. The
        // synthesized field's body is constructed from already-validated
        // variant names, so collect_derived can't fail.
        let _ = env;
    }
}

/// walk an `EExpr` and collect every bare `Var`
/// name that appears free (i.e., not shadowed by an enclosing binder).
/// Used by the derived-field acyclicity check to detect intra-scope
/// references from one derived field to another.
///
/// must track binders. Constructs that
/// introduce new names — quantifiers, let bindings, lambdas, match
/// arms with pattern-bound names, and `var` declarations — must
/// exclude their bound names from the collected set so that bodies
/// like `derived a = all a: Int | a > 0` are not falsely flagged as
/// self-cycles.
///
/// The walker is exhaustive over `EExpr` variants so the compiler
/// catches any newly-added variant.
pub(super) fn collect_var_names(expr: &EExpr, into: &mut HashSet<String>) {
    let mut bound: HashSet<String> = HashSet::new();
    collect_var_names_inner(expr, &mut bound, into);
}

pub(super) fn collect_var_names_inner(
    expr: &EExpr,
    bound: &mut HashSet<String>,
    into: &mut HashSet<String>,
) {
    match expr {
        EExpr::Var(_, name, _) => {
            if !bound.contains(name) {
                into.insert(name.clone());
            }
        }
        EExpr::Lit(_, _, _)
        | EExpr::Sorry(_)
        | EExpr::Todo(_)
        | EExpr::Unresolved(_, _)
        | EExpr::Qual(_, _, _, _) => {}
        EExpr::Field(_, e, _, _)
        | EExpr::Prime(_, e, _)
        | EExpr::Always(_, e, _)
        | EExpr::Eventually(_, e, _)
        | EExpr::Historically(_, e, _)
        | EExpr::Once(_, e, _)
        | EExpr::Previously(_, e, _)
        | EExpr::Assert(_, e, _)
        | EExpr::Assume(_, e, _)
        | EExpr::NamedPair(_, _, e, _)
        | EExpr::Card(_, e, _)
        | EExpr::UnOp(_, _, e, _) => collect_var_names_inner(e, bound, into),
        EExpr::BinOp(_, _, l, r, _)
        | EExpr::Until(_, l, r, _)
        | EExpr::Since(_, l, r, _)
        | EExpr::Assign(_, l, r, _)
        | EExpr::Seq(_, l, r, _)
        | EExpr::SameStep(_, l, r, _)
        | EExpr::In(_, l, r, _)
        | EExpr::Pipe(_, l, r, _)
        | EExpr::Index(_, l, r, _) => {
            collect_var_names_inner(l, bound, into);
            collect_var_names_inner(r, bound, into);
        }
        EExpr::MapUpdate(_, m, k, v, _) => {
            collect_var_names_inner(m, bound, into);
            collect_var_names_inner(k, bound, into);
            collect_var_names_inner(v, bound, into);
        }
        EExpr::Call(_, callee, args, _) => {
            collect_var_names_inner(callee, bound, into);
            for a in args {
                collect_var_names_inner(a, bound, into);
            }
        }
        EExpr::CallR(_, callee, refs, args, _) => {
            collect_var_names_inner(callee, bound, into);
            for r in refs {
                collect_var_names_inner(r, bound, into);
            }
            for a in args {
                collect_var_names_inner(a, bound, into);
            }
        }
        EExpr::QualCall(_, _, _, args, _) => {
            for a in args {
                collect_var_names_inner(a, bound, into);
            }
        }
        // bind the quantifier variable
        // before walking the body.
        EExpr::Quant(_, _, var_name, _, body, _) => {
            let was_new = bound.insert(var_name.clone());
            collect_var_names_inner(body, bound, into);
            if was_new {
                bound.remove(var_name);
            }
        }
        EExpr::Choose(_, binder, _, predicate, _) => {
            let was_new = bound.insert(binder.clone());
            if let Some(pred) = predicate {
                collect_var_names_inner(pred, bound, into);
            }
            if was_new {
                bound.remove(binder);
            }
        }
        // each `let` binding introduces
        // its name into scope for subsequent bindings AND the body.
        EExpr::Let(bindings, body, _) => {
            let mut added: Vec<String> = Vec::new();
            for (name, _, rhs) in bindings {
                collect_var_names_inner(rhs, bound, into);
                if bound.insert(name.clone()) {
                    added.push(name.clone());
                }
            }
            collect_var_names_inner(body, bound, into);
            for name in added {
                bound.remove(&name);
            }
        }
        // lambda parameters bind in the body.
        EExpr::Lam(params, _, body, _) => {
            let mut added: Vec<String> = Vec::new();
            for (name, _) in params {
                if bound.insert(name.clone()) {
                    added.push(name.clone());
                }
            }
            collect_var_names_inner(body, bound, into);
            for name in added {
                bound.remove(&name);
            }
        }
        // match arm patterns bind names
        // for the duration of the arm body and guard.
        EExpr::Match(scrut, arms, _) => {
            collect_var_names_inner(scrut, bound, into);
            for (pat, guard, body) in arms {
                let mut pat_names: Vec<String> = Vec::new();
                collect_pattern_names(pat, &mut pat_names);
                let mut added: Vec<String> = Vec::new();
                for name in &pat_names {
                    if bound.insert(name.clone()) {
                        added.push(name.clone());
                    }
                }
                if let Some(g) = guard {
                    collect_var_names_inner(g, bound, into);
                }
                collect_var_names_inner(body, bound, into);
                for name in added {
                    bound.remove(&name);
                }
            }
        }
        EExpr::TupleLit(_, items, _)
        | EExpr::SetLit(_, items, _)
        | EExpr::SeqLit(_, items, _)
        | EExpr::Block(items, _) => {
            for item in items {
                collect_var_names_inner(item, bound, into);
            }
        }
        // set comprehension binds the
        // comprehension variable in head and predicate.
        EExpr::SetComp(_, head, comp_var, _, source, pred, _) => {
            if let Some(source) = source {
                collect_var_names_inner(source, bound, into);
            }
            let was_new = bound.insert(comp_var.clone());
            if let Some(h) = head {
                collect_var_names_inner(h, bound, into);
            }
            collect_var_names_inner(pred, bound, into);
            if was_new {
                bound.remove(comp_var);
            }
        }
        EExpr::RelComp(_, projection, bindings, filter, _) => {
            let mut added = Vec::new();
            for binding in bindings {
                if let Some(source) = &binding.source {
                    collect_var_names_inner(source, bound, into);
                }
                if bound.insert(binding.var.clone()) {
                    added.push(binding.var.clone());
                }
            }
            collect_var_names_inner(projection, bound, into);
            collect_var_names_inner(filter, bound, into);
            for name in added {
                bound.remove(&name);
            }
        }
        EExpr::MapLit(_, kvs, _) => {
            for (k, v) in kvs {
                collect_var_names_inner(k, bound, into);
                collect_var_names_inner(v, bound, into);
            }
        }
        // `var name = init; rest` binds
        // `name` in the rest. The init expression sees the prior scope.
        EExpr::VarDecl(name, _, init, rest, _) => {
            collect_var_names_inner(init, bound, into);
            let was_new = bound.insert(name.clone());
            collect_var_names_inner(rest, bound, into);
            if was_new {
                bound.remove(name);
            }
        }
        EExpr::While(cond, _contracts, body, _) => {
            collect_var_names_inner(cond, bound, into);
            collect_var_names_inner(body, bound, into);
        }
        EExpr::IfElse(cond, then_b, else_b, _) => {
            collect_var_names_inner(cond, bound, into);
            collect_var_names_inner(then_b, bound, into);
            if let Some(e) = else_b {
                collect_var_names_inner(e, bound, into);
            }
        }
        EExpr::Saw(_, _, _, args, _) => {
            for e in args.iter().flatten() {
                collect_var_names_inner(e, bound, into);
            }
        }
        EExpr::CtorRecord(_, _, _, fields, _) | EExpr::StructCtor(_, _, fields, _) => {
            for (_, v) in fields {
                collect_var_names_inner(v, bound, into);
            }
        }
        EExpr::Aggregate(_, _, var_name, _, body, in_filter, _) => {
            let was_new = bound.insert(var_name.clone());
            collect_var_names_inner(body, bound, into);
            if let Some(f) = in_filter {
                collect_var_names_inner(f, bound, into);
            }
            if was_new {
                bound.remove(var_name);
            }
        }
    }
}

/// Walk an `EPattern` and collect all `Var`-bound names that the
/// pattern introduces. Used by the binder-tracking walker so that
/// match arm pattern variables shadow outer references.
pub(super) fn collect_pattern_names(pat: &EPattern, into: &mut Vec<String>) {
    match pat {
        EPattern::Var(name) => into.push(name.clone()),
        EPattern::Wild => {}
        EPattern::Ctor(_, fields) => {
            for (_, sub) in fields {
                collect_pattern_names(sub, into);
            }
        }
        EPattern::Or(l, r) => {
            collect_pattern_names(l, into);
            collect_pattern_names(r, into);
        }
    }
}

/// detect cycles in a set of derived fields.
/// Returns the cycle path (list of names) if a cycle is found,
/// otherwise `None`. The path is in the order `a -> b -> c -> a`
/// suitable for `messages::derived_cycle`.
///
/// Algorithm: build a name → references-on-same-scope map, then DFS
/// from each derived field tracking the visit stack. A back-edge to
/// any name on the stack is a cycle.
pub(super) fn detect_derived_cycle(derived_fields: &[EDerived]) -> Option<Vec<String>> {
    let names: HashSet<String> = derived_fields.iter().map(|d| d.name.clone()).collect();

    // Adjacency list: derived name → derived names referenced from its body.
    let mut edges: HashMap<String, Vec<String>> = HashMap::new();
    for d in derived_fields {
        let mut refs = HashSet::new();
        collect_var_names(&d.body, &mut refs);
        let intra: Vec<String> = refs.into_iter().filter(|n| names.contains(n)).collect();
        edges.insert(d.name.clone(), intra);
    }

    // DFS from each node, tracking the current visit stack to detect
    // cycles. `visited` marks nodes we've fully explored (no cycle
    // through them); `stack` is the current DFS path.
    let mut visited: HashSet<String> = HashSet::new();
    for start in edges.keys() {
        let mut stack: Vec<String> = Vec::new();
        if let Some(cycle) = dfs_cycle(start, &edges, &mut visited, &mut stack) {
            return Some(cycle);
        }
    }
    None
}

pub(super) fn dfs_cycle(
    node: &str,
    edges: &HashMap<String, Vec<String>>,
    visited: &mut HashSet<String>,
    stack: &mut Vec<String>,
) -> Option<Vec<String>> {
    if let Some(idx) = stack.iter().position(|n| n == node) {
        // Back-edge: extract the cycle from the stack and append the
        // back-edge target to close the loop visually.
        let mut cycle: Vec<String> = stack[idx..].to_vec();
        cycle.push(node.to_owned());
        return Some(cycle);
    }
    if visited.contains(node) {
        return None;
    }
    stack.push(node.to_owned());
    if let Some(neighbors) = edges.get(node) {
        for next in neighbors {
            if let Some(cycle) = dfs_cycle(next, edges, visited, stack) {
                return Some(cycle);
            }
        }
    }
    stack.pop();
    visited.insert(node.to_owned());
    None
}

pub(super) fn collect_field(f: &ast::FieldDecl) -> EField {
    let default = match &f.default {
        Some(ast::FieldDefault::Value(expr)) => Some(EFieldDefault::Value(collect_expr(expr))),
        Some(ast::FieldDefault::In(exprs)) => {
            let collected: Vec<EExpr> = exprs.iter().map(collect_expr).collect();
            if collected.len() == 1 {
                // Single-value `in` is equivalent to `= value`
                Some(EFieldDefault::Value(collected.into_iter().next().unwrap()))
            } else {
                Some(EFieldDefault::In(collected))
            }
        }
        Some(ast::FieldDefault::Where(expr)) => Some(EFieldDefault::Where(collect_expr(expr))),
        None => None,
    };
    EField {
        name: f.name.clone(),
        ty: resolve_type_ref(&f.ty),
        default,
        span: Some(f.span),
    }
}

pub(super) fn collect_action(a: &ast::EntityAction) -> EAction {
    let refs: Vec<(String, Ty)> = a
        .ref_params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    let params: Vec<(String, Ty)> = a
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    let requires: Vec<EExpr> = a
        .contracts
        .iter()
        .filter_map(|c| match c {
            ast::Contract::Requires { expr, .. } => Some(collect_expr(expr)),
            _ => None,
        })
        .collect();
    let ensures: Vec<EExpr> = a
        .contracts
        .iter()
        .filter_map(|c| match c {
            ast::Contract::Ensures { expr, .. } => Some(collect_expr(expr)),
            _ => None,
        })
        .collect();
    let body: Vec<EExpr> = a.body.iter().map(collect_expr).collect();
    EAction {
        name: a.name.clone(),
        refs,
        params,
        requires,
        ensures,
        body,
        span: Some(a.span),
    }
}

pub(super) fn collect_invoc_arg(arg: &ast::InvocArg) -> EExpr {
    let unresolved = Ty::Error;
    match arg {
        ast::InvocArg::Field { obj, field, .. } => EExpr::Field(
            unresolved.clone(),
            Box::new(EExpr::Var(unresolved, obj.clone(), None)),
            field.clone(),
            None,
        ),
        ast::InvocArg::Simple { name, .. } | ast::InvocArg::State { name, .. } => {
            EExpr::Var(unresolved, name.clone(), None)
        }
        ast::InvocArg::Int { value, .. } => {
            EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(*value), None)
        }
        ast::InvocArg::Real { value, .. } => {
            EExpr::Lit(Ty::Builtin(BuiltinTy::Real), Literal::Real(*value), None)
        }
        ast::InvocArg::Float { value, .. } => {
            let v = parse_float_text(value);
            EExpr::Lit(Ty::Builtin(BuiltinTy::Float), Literal::Float(v), None)
        }
        ast::InvocArg::Str { value, .. } => EExpr::Lit(
            Ty::Builtin(BuiltinTy::String),
            Literal::Str(value.clone()),
            None,
        ),
    }
}
