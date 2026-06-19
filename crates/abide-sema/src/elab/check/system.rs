//! System well-formedness checking.

use std::collections::{HashMap, HashSet};

use super::super::env::Env;
use super::super::error::{ElabError, ErrorKind};
use super::super::types::{
    ECommand, EEventAction, EExpr, EExtern, EExternAssume, EMatchScrutinee, EProcDepCond, EQuery,
    ESystem, Ty,
};
use super::matches::{check_pattern_shape, resolve_to_enum_info};

pub(super) fn check_system(env: &Env, system: &ESystem) -> Vec<ElabError> {
    let mut errors = Vec::new();
    let sys_ctx = format!("system {}", system.name);

    let entity_names: Vec<String> = env.entities.keys().cloned().collect();
    // Also accept canonical entity names (the entity's declared name may differ
    // from the working namespace key when imported via alias).
    let canonical_names: std::collections::HashSet<String> =
        env.entities.values().map(|e| e.name.clone()).collect();
    for store in &system.store_params {
        if env.lookup_entity(&store.entity_type).is_none()
            && !canonical_names.contains(&store.entity_type)
        {
            let mut err = if let Some(span) = system.span {
                ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "system {} uses unknown entity '{}'",
                        system.name, store.entity_type
                    ),
                    &sys_ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::UndefinedRef,
                    format!(
                        "system {} uses unknown entity '{}'",
                        system.name, store.entity_type
                    ),
                    &sys_ctx,
                )
            };
            if let Some(closest) = super::find_closest_name(&store.entity_type, &entity_names) {
                err = err.with_help(format!("did you mean '{closest}'?"));
            }
            errors.push(err);
        }
        if let (Some(lo), Some(hi)) = (store.lo, store.hi) {
            if lo < 0 || hi < 0 || lo > hi {
                errors.push(ElabError::with_span(
                    ErrorKind::TypeMismatch,
                    format!(
                        "system `{}` store parameter `{}` has invalid bounds [{lo}..{hi}]",
                        system.name, store.name
                    ),
                    &sys_ctx,
                    system
                        .span
                        .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                ));
            }
        }
    }

    let mut seen_deps = HashSet::new();
    for dep in &system.deps {
        if !seen_deps.insert(dep.clone()) {
            errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!("system `{}` declares duplicate dep `{dep}`", system.name),
                &sys_ctx,
                system
                    .span
                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
            ));
        }
        if !env.externs.contains_key(dep) {
            errors.push(
                ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "system `{}` declares unknown extern dep `{dep}`",
                        system.name
                    ),
                    &sys_ctx,
                    system
                        .span
                        .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                )
                .with_help(
                    "`dep` declarations are validation-only metadata for authorizing calls to \
                 declared `extern` blocks; a `dep` does not import, does not instantiate, \
                 and does not add verifier semantics for the named extern.",
                ),
            );
        }
    }

    let system_queries = implemented_queries_from_system(&system.queries);
    if !check_interface_conformance(
        env,
        InterfaceConformanceTarget {
            decl_kind: "system",
            decl_name: &system.name,
            implements: system.implements.as_deref(),
            commands: &system.commands,
            queries: &system_queries,
            ctx: &sys_ctx,
            fallback_span: system.span,
        },
        &mut errors,
    ) {
        return errors;
    }

    for step in &system.actions {
        let crosscall_ctx = CrossCallValidationCtx {
            env,
            system_name: &system.name,
            sys_ctx: &sys_ctx,
            deps: &system.deps,
            fallback_span: step.span.or(system.span),
        };
        validate_crosscalls_in_actions(
            &crosscall_ctx,
            &step.body,
            &mut errors,
            &mut HashMap::new(),
        );
    }

    for scope in &system.scopes {
        if scope.lo < 0 || scope.hi < scope.lo {
            let err = if let Some(span) = system.span {
                ElabError::with_span(
                    ErrorKind::InvalidScope,
                    format!(
                        "scope {} has invalid range {}..{}",
                        scope.entity, scope.lo, scope.hi
                    ),
                    &sys_ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::InvalidScope,
                    format!(
                        "scope {} has invalid range {}..{}",
                        scope.entity, scope.lo, scope.hi
                    ),
                    &sys_ctx,
                )
            };
            errors.push(err);
        }
    }

    // invariants are safety-only — liveness
    // temporal operators (`eventually`, `until`, `previously`, `since`)
    // are not allowed in system invariant bodies either.
    for inv in &system.invariants {
        super::check_invariant_body_state_only(&inv.body, &mut errors);
    }

    // validate struct constructor defaults on system fields.
    for field in &system.fields {
        if let Some(super::super::types::EFieldDefault::Value(EExpr::StructCtor(
            _,
            struct_name,
            ctor_fields,
            span,
        ))) = &field.default
        {
            if let Ty::Record(_, declared_fields) = &field.ty {
                let declared_names: HashSet<&str> =
                    declared_fields.iter().map(|(n, _)| n.as_str()).collect();
                let mut seen = HashSet::new();
                for (fname, _) in ctor_fields {
                    if !declared_names.contains(fname.as_str()) {
                        errors.push(ElabError::with_span(
                            ErrorKind::UndefinedRef,
                            format!(
                                "unknown field `{fname}` in struct constructor `{struct_name}`"
                            ),
                            &sys_ctx,
                            span.or(system.span)
                                .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    }
                    if !seen.insert(fname.as_str()) {
                        errors.push(ElabError::with_span(
                            ErrorKind::DuplicateDecl,
                            format!(
                                "duplicate field `{fname}` in struct constructor `{struct_name}`"
                            ),
                            &sys_ctx,
                            span.or(system.span)
                                .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    }
                }
                let provided: HashSet<&str> = ctor_fields.iter().map(|(n, _)| n.as_str()).collect();
                for (dname, _) in declared_fields {
                    if !provided.contains(dname.as_str()) {
                        errors.push(ElabError::with_span(
                            ErrorKind::MissingField,
                            format!(
                                "missing field `{dname}` in struct constructor `{struct_name}`; \
                                 the system field will be unconstrained at initial state"
                            ),
                            &sys_ctx,
                            span.or(system.span)
                                .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    }
                }
            }
        }
    }

    // validate return type / return expression consistency.
    // Build command return type map for lookup.
    let cmd_return_types: HashMap<&str, Option<&Ty>> = system
        .commands
        .iter()
        .map(|c| (c.name.as_str(), c.return_type.as_ref()))
        .collect();
    for step in &system.actions {
        let cmd_rt = cmd_return_types.get(step.name.as_str()).copied().flatten();
        let step_span = step
            .span
            .or(system.span)
            .unwrap_or(crate::span::Span { start: 0, end: 0 });
        match (&step.return_expr, cmd_rt) {
            // Step has return but command has no return type
            (Some(_), None) => {
                errors.push(ElabError::with_span(
                    ErrorKind::TypeMismatch,
                    format!(
                        "action `{}` has a `return` expression but command `{}` \
                         does not declare a return type",
                        step.name, step.name
                    ),
                    &sys_ctx,
                    step_span,
                ));
            }
            // Both present and return type is enum: validate the return
            // expression is a variant of the declared enum, with correct arity.
            (Some(ret_expr), Some(Ty::Enum(enum_name, variants))) => {
                let ctor_name = extract_return_ctor_name(ret_expr);
                if let Some(ref name) = ctor_name {
                    if variants.contains(name) {
                        // Variant name is valid — check payload arity and types.
                        let payload = extract_return_payload(ret_expr);
                        let declared_fields: Vec<(String, Ty)> = env
                            .variant_fields
                            .get(enum_name)
                            .and_then(|vfs| {
                                vfs.iter()
                                    .find(|(vn, _)| vn == name)
                                    .map(|(_, fs)| fs.clone())
                            })
                            // abide-audit: allow-silent-fallback -- empty collection/string is the documented neutral value for this path
                            .unwrap_or_default();
                        match payload {
                            ReturnPayload::Positional(args) => {
                                if args.len() == declared_fields.len() {
                                    for (i, (arg, (fname, declared_ty))) in
                                        args.iter().zip(declared_fields.iter()).enumerate()
                                    {
                                        let arg_ty = arg.ty();
                                        if !matches!(&arg_ty, Ty::Error)
                                            && !matches!(declared_ty, Ty::Error)
                                            && !super::expr_compatible_with_ty(arg, declared_ty)
                                        {
                                            errors.push(ElabError::with_span(
                                                ErrorKind::TypeMismatch,
                                                format!(
                                                    "action `{}` returns `@{name}` with argument {} \
                                                     (field `{fname}`) of type `{}` but variant \
                                                     `{enum_name}::@{name}` expects `{}`",
                                                    step.name,
                                                    i + 1,
                                                    arg_ty.name(),
                                                    declared_ty.name()
                                                ),
                                                &sys_ctx,
                                                step_span,
                                            ));
                                        }
                                    }
                                } else {
                                    errors.push(ElabError::with_span(
                                        ErrorKind::ParamMismatch,
                                        format!(
                                            "action `{}` returns `@{name}` with {} \
                                             argument(s) but variant `{enum_name}::@{name}` \
                                             expects {}",
                                            step.name,
                                            args.len(),
                                            declared_fields.len()
                                        ),
                                        &sys_ctx,
                                        step_span,
                                    ));
                                }
                            }
                            ReturnPayload::Named(named_args) => {
                                // Match by field name, not position.
                                let decl_map: HashMap<&str, &Ty> = declared_fields
                                    .iter()
                                    .map(|(n, t)| (n.as_str(), t))
                                    .collect();
                                if named_args.len() != declared_fields.len() {
                                    errors.push(ElabError::with_span(
                                        ErrorKind::ParamMismatch,
                                        format!(
                                            "action `{}` returns `@{name}` with {} \
                                             field(s) but variant `{enum_name}::@{name}` \
                                             expects {}",
                                            step.name,
                                            named_args.len(),
                                            declared_fields.len()
                                        ),
                                        &sys_ctx,
                                        step_span,
                                    ));
                                }
                                for (fname, arg) in &named_args {
                                    if let Some(declared_ty) = decl_map.get(fname) {
                                        let arg_ty = arg.ty();
                                        if !matches!(&arg_ty, Ty::Error)
                                            && !matches!(declared_ty, Ty::Error)
                                            && !super::expr_compatible_with_ty(arg, declared_ty)
                                        {
                                            errors.push(ElabError::with_span(
                                                ErrorKind::TypeMismatch,
                                                format!(
                                                    "action `{}` returns `@{name}` with field \
                                                     `{fname}` of type `{}` but variant \
                                                     `{enum_name}::@{name}` expects `{}`",
                                                    step.name,
                                                    arg_ty.name(),
                                                    declared_ty.name()
                                                ),
                                                &sys_ctx,
                                                step_span,
                                            ));
                                        }
                                    } else {
                                        errors.push(ElabError::with_span(
                                            ErrorKind::UndefinedRef,
                                            format!(
                                                "action `{}` returns `@{name}` with unknown \
                                                 field `{fname}` (variant `{enum_name}::@{name}` \
                                                 has fields: {})",
                                                step.name,
                                                declared_fields
                                                    .iter()
                                                    .map(|(n, _)| n.as_str())
                                                    .collect::<Vec<_>>()
                                                    .join(", ")
                                            ),
                                            &sys_ctx,
                                            step_span,
                                        ));
                                    }
                                }
                            }
                        }
                    } else {
                        errors.push(ElabError::with_span(
                            ErrorKind::TypeMismatch,
                            format!(
                                "action `{}` returns `@{name}` which is not a variant of \
                                 `{enum_name}`; expected one of: {}",
                                step.name,
                                variants
                                    .iter()
                                    .map(|v| format!("@{v}"))
                                    .collect::<Vec<_>>()
                                    .join(", ")
                            ),
                            &sys_ctx,
                            step_span,
                        ));
                    }
                } else {
                    // Return expression is not a constructor — invalid for
                    // an enum return type.
                    errors.push(ElabError::with_span(
                        ErrorKind::TypeMismatch,
                        format!(
                            "action `{}` returns a non-constructor expression but \
                             command `{}` expects return type `{enum_name}` \
                             (an enum); use `return @variant` or `return @variant(...)`",
                            step.name, step.name
                        ),
                        &sys_ctx,
                        step_span,
                    ));
                }
            }
            _ => {}
        }
    }

    // validate proc declarations.
    // Build let-binding map: instance_name → system_type
    let mut let_binding_systems: HashMap<&str, &str> = system
        .let_bindings
        .iter()
        .map(|lb| (lb.name.as_str(), lb.system_type.as_str()))
        .collect();
    let_binding_systems
        .entry("self")
        .or_insert_with(|| system.name.as_str());
    for proc in &system.procs {
        let proc_ctx = format!("proc {}", proc.name);
        let span = proc
            .span
            .or(system.span)
            .unwrap_or(crate::span::Span { start: 0, end: 0 });
        let proc_param_names: HashSet<&str> = proc.params.iter().map(|(n, _)| n.as_str()).collect();

        if let Some(req) = &proc.requires {
            if !super::is_bool_expr(req) {
                errors.push(ElabError::with_span(
                    ErrorKind::TypeMismatch,
                    crate::messages::MSG_REQUIRES_SHOULD_BE_BOOL,
                    &proc_ctx,
                    span,
                ));
            }
        }

        // Collect declared node names for edge validation.
        let mut node_names: HashSet<&str> = HashSet::new();
        for node in &proc.nodes {
            if !node_names.insert(node.name.as_str()) {
                errors.push(ElabError::with_span(
                    ErrorKind::DuplicateDecl,
                    format!("duplicate proc node `{}`", node.name),
                    &proc_ctx,
                    span,
                ));
            }
            if proc_param_names.contains(node.name.as_str()) {
                errors.push(ElabError::with_span(
                    ErrorKind::DuplicateDecl,
                    format!(
                        "proc node `{}` conflicts with proc parameter `{}`",
                        node.name, node.name
                    ),
                    &proc_ctx,
                    span,
                ));
            }
            // Validate instance handle exists as a let binding.
            if let Some(sys_type) = let_binding_systems.get(node.instance.as_str()) {
                // Validate command exists on the bound system.
                if let Some(bound_sys) = env.systems.get(*sys_type) {
                    if let Some(cmd) = bound_sys.commands.iter().find(|c| c.name == node.command) {
                        // Validate argument arity and types.
                        if node.args.len() == cmd.params.len() {
                            for (i, ((_, param_ty), arg)) in
                                cmd.params.iter().zip(node.args.iter()).enumerate()
                            {
                                let arg_ty = arg.ty();
                                if !matches!(&arg_ty, Ty::Error)
                                    && !matches!(param_ty, Ty::Error)
                                    && !super::expr_compatible_with_ty(arg, param_ty)
                                {
                                    errors.push(ElabError::with_span(
                                        ErrorKind::TypeMismatch,
                                        format!(
                                            "proc node `{}` passes argument {} of type `{}` \
                                             to command `{}` which expects `{}`",
                                            node.name,
                                            i + 1,
                                            arg_ty.name(),
                                            node.command,
                                            param_ty.name()
                                        ),
                                        &proc_ctx,
                                        span,
                                    ));
                                }
                            }
                        } else {
                            errors.push(ElabError::with_span(
                                ErrorKind::ParamMismatch,
                                format!(
                                    "proc node `{}` passes {} argument(s) to command `{}` \
                                     but it expects {}",
                                    node.name,
                                    node.args.len(),
                                    node.command,
                                    cmd.params.len()
                                ),
                                &proc_ctx,
                                span,
                            ));
                        }
                    } else {
                        errors.push(ElabError::with_span(
                            ErrorKind::UndefinedRef,
                            format!(
                                "proc node `{}` references command `{}` which does not exist on system `{sys_type}`",
                                node.name, node.command
                            ),
                            &proc_ctx,
                            span,
                        ));
                    }
                }
            } else {
                errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "proc node `{}` references instance `{}` which is neither `self` nor a let binding in this program",
                        node.name, node.instance
                    ),
                    &proc_ctx,
                    span,
                ));
            }
        }

        // Validate edges: target must be declared and dependency conditions must
        // reference declared nodes and valid outcome ports.
        let proc_dep_check_ctx = ProcDepCheckCtx {
            env,
            proc,
            node_names: &node_names,
            let_binding_systems: &let_binding_systems,
            proc_ctx: &proc_ctx,
            span,
        };
        for edge in &proc.edges {
            if !node_names.contains(edge.target.as_str()) {
                errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "needs edge target `{}` is not a declared node in proc `{}`",
                        edge.target, proc.name
                    ),
                    &proc_ctx,
                    span,
                ));
            }
            validate_proc_dep_cond(&proc_dep_check_ctx, &edge.condition, &mut errors);
        }

        // Cycle detection: build adjacency list and do DFS.
        let mut adj: HashMap<&str, Vec<&str>> = HashMap::new();
        for node in &proc.nodes {
            adj.entry(node.name.as_str()).or_default();
        }
        for edge in &proc.edges {
            let mut refs = Vec::new();
            collect_proc_dep_sources(&edge.condition, &mut refs);
            for source in refs {
                adj.entry(source).or_default().push(edge.target.as_str());
            }
        }
        // DFS-based cycle detection.
        let mut visited: HashSet<&str> = HashSet::new();
        let mut on_stack: HashSet<&str> = HashSet::new();
        let mut has_cycle = false;
        fn dfs<'a>(
            node: &'a str,
            adj: &HashMap<&'a str, Vec<&'a str>>,
            visited: &mut HashSet<&'a str>,
            on_stack: &mut HashSet<&'a str>,
        ) -> bool {
            if on_stack.contains(node) {
                return true;
            }
            if visited.contains(node) {
                return false;
            }
            visited.insert(node);
            on_stack.insert(node);
            if let Some(neighbors) = adj.get(node) {
                for &next in neighbors {
                    if dfs(next, adj, visited, on_stack) {
                        return true;
                    }
                }
            }
            on_stack.remove(node);
            false
        }
        for node_name in &node_names {
            if !visited.contains(node_name) && dfs(node_name, &adj, &mut visited, &mut on_stack) {
                has_cycle = true;
                break;
            }
        }
        if has_cycle {
            errors.push(ElabError::with_span(
                ErrorKind::CyclicDefinition,
                format!("proc `{}` contains a dependency cycle", proc.name),
                &proc_ctx,
                span,
            ));
        }
    }

    errors
}

struct ImplementedQuery {
    name: String,
    params: Vec<(String, Ty)>,
    return_type: Ty,
    span: Option<crate::span::Span>,
}

struct InterfaceConformanceTarget<'a> {
    decl_kind: &'a str,
    decl_name: &'a str,
    implements: Option<&'a str>,
    commands: &'a [ECommand],
    queries: &'a [ImplementedQuery],
    ctx: &'a str,
    fallback_span: Option<crate::span::Span>,
}

fn implemented_queries_from_system(queries: &[EQuery]) -> Vec<ImplementedQuery> {
    queries
        .iter()
        .map(|query| ImplementedQuery {
            name: query.name.clone(),
            params: query.params.clone(),
            return_type: query.body.ty(),
            span: query.span,
        })
        .collect()
}

fn resolve_type_for_compatibility(env: &Env, ty: &Ty) -> Ty {
    fn resolve(env: &Env, ty: &Ty, seen: &mut HashSet<String>) -> Ty {
        match ty {
            Ty::Named(name) => {
                let canonical_name = env.aliases.get(name).unwrap_or(name);
                if !seen.insert(canonical_name.clone()) {
                    return ty.clone();
                }
                if let Some(resolved) = env.lookup_type(canonical_name) {
                    resolve(env, resolved, seen)
                } else if let Some(entity) = env.lookup_entity(canonical_name) {
                    Ty::Entity(entity.name.clone())
                } else {
                    Ty::Named(canonical_name.clone())
                }
            }
            Ty::Record(name, fields) => Ty::Record(
                name.clone(),
                fields
                    .iter()
                    .map(|(field, field_ty)| (field.clone(), resolve(env, field_ty, seen)))
                    .collect(),
            ),
            Ty::Alias(name, inner) => Ty::Alias(name.clone(), Box::new(resolve(env, inner, seen))),
            Ty::Newtype(name, inner) => {
                Ty::Newtype(name.clone(), Box::new(resolve(env, inner, seen)))
            }
            Ty::Param(name, args) => Ty::Param(
                name.clone(),
                args.iter().map(|arg| resolve(env, arg, seen)).collect(),
            ),
            Ty::Fn(arg, ret) => Ty::Fn(
                Box::new(resolve(env, arg, seen)),
                Box::new(resolve(env, ret, seen)),
            ),
            Ty::Set(inner) => Ty::Set(Box::new(resolve(env, inner, seen))),
            Ty::Seq(inner) => Ty::Seq(Box::new(resolve(env, inner, seen))),
            Ty::Map(key, value) => Ty::Map(
                Box::new(resolve(env, key, seen)),
                Box::new(resolve(env, value, seen)),
            ),
            Ty::Relation(columns) => Ty::Relation(
                columns
                    .iter()
                    .map(|column| resolve(env, column, seen))
                    .collect(),
            ),
            Ty::Tuple(elements) => Ty::Tuple(
                elements
                    .iter()
                    .map(|element| resolve(env, element, seen))
                    .collect(),
            ),
            Ty::Refinement(base, pred) => {
                Ty::Refinement(Box::new(resolve(env, base, seen)), pred.clone())
            }
            _ => ty.clone(),
        }
    }

    resolve(env, ty, &mut HashSet::new())
}

fn types_compatible_in_env(env: &Env, implemented: &Ty, expected: &Ty) -> bool {
    let implemented = resolve_type_for_compatibility(env, implemented);
    let expected = resolve_type_for_compatibility(env, expected);
    super::types_compatible(&implemented, &expected)
}

fn check_interface_conformance(
    env: &Env,
    target: InterfaceConformanceTarget<'_>,
    errors: &mut Vec<ElabError>,
) -> bool {
    let Some(interface_name) = target.implements else {
        return true;
    };
    let Some(interface) = env.interfaces.get(interface_name) else {
        let message = format!(
            "{} {} implements unknown interface `{interface_name}`",
            target.decl_kind, target.decl_name
        );
        let err = if let Some(span) = target.fallback_span {
            ElabError::with_span(ErrorKind::UndefinedRef, message, target.ctx, span)
        } else {
            ElabError::new(ErrorKind::UndefinedRef, message, target.ctx)
        };
        errors.push(err);
        return false;
    };

    for iface_cmd in &interface.commands {
        match target
            .commands
            .iter()
            .find(|cmd| cmd.name == iface_cmd.name)
        {
            Some(implemented_cmd) => {
                if implemented_cmd.params.len() != iface_cmd.params.len() {
                    errors.push(ElabError::with_span(
                        ErrorKind::ParamMismatch,
                        format!(
                            "{} `{}` command `{}` has {} parameter(s), but interface `{}` requires {}",
                            target.decl_kind,
                            target.decl_name,
                            iface_cmd.name,
                            implemented_cmd.params.len(),
                            interface.name,
                            iface_cmd.params.len()
                        ),
                        target.ctx,
                        implemented_cmd
                            .span
                            .or(target.fallback_span)
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                } else {
                    for (idx, (implemented_param, iface_param)) in implemented_cmd
                        .params
                        .iter()
                        .zip(iface_cmd.params.iter())
                        .enumerate()
                    {
                        if !types_compatible_in_env(env, &implemented_param.1, &iface_param.1) {
                            errors.push(ElabError::with_span(
                                ErrorKind::TypeMismatch,
                                format!(
                                    "{} `{}` command `{}` parameter {} has type `{}` but interface `{}` requires `{}`",
                                    target.decl_kind,
                                    target.decl_name,
                                    iface_cmd.name,
                                    idx + 1,
                                    implemented_param.1.name(),
                                    interface.name,
                                    iface_param.1.name()
                                ),
                                target.ctx,
                                implemented_cmd
                                    .span
                                    .or(target.fallback_span)
                                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                            ));
                        }
                    }
                }

                match (&implemented_cmd.return_type, &iface_cmd.return_type) {
                    (Some(implemented_ret), Some(iface_ret))
                        if !matches!(implemented_ret, Ty::Error)
                            && !matches!(iface_ret, Ty::Error)
                            && !types_compatible_in_env(env, implemented_ret, iface_ret) =>
                    {
                        errors.push(ElabError::with_span(
                            ErrorKind::TypeMismatch,
                            format!(
                                "{} `{}` command `{}` returns `{}` but interface `{}` requires `{}`",
                                target.decl_kind,
                                target.decl_name,
                                iface_cmd.name,
                                implemented_ret.name(),
                                interface.name,
                                iface_ret.name()
                            ),
                            target.ctx,
                            implemented_cmd
                                .span
                                .or(target.fallback_span)
                                .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    }
                    (None, Some(iface_ret)) => {
                        errors.push(ElabError::with_span(
                            ErrorKind::TypeMismatch,
                            format!(
                                "{} `{}` command `{}` has no return type but interface `{}` requires `{}`",
                                target.decl_kind,
                                target.decl_name,
                                iface_cmd.name,
                                interface.name,
                                iface_ret.name()
                            ),
                            target.ctx,
                            implemented_cmd
                                .span
                                .or(target.fallback_span)
                                .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    }
                    (Some(implemented_ret), None) if !matches!(implemented_ret, Ty::Error) => {
                        errors.push(ElabError::with_span(
                            ErrorKind::TypeMismatch,
                            format!(
                                "{} `{}` command `{}` returns `{}` but interface `{}` declares no return value",
                                target.decl_kind,
                                target.decl_name,
                                iface_cmd.name,
                                implemented_ret.name(),
                                interface.name
                            ),
                            target.ctx,
                            implemented_cmd
                                .span
                                .or(target.fallback_span)
                                .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    }
                    _ => {}
                }
            }
            None => {
                errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "{} `{}` is missing command `{}` required by interface `{}`",
                        target.decl_kind, target.decl_name, iface_cmd.name, interface.name
                    ),
                    target.ctx,
                    target
                        .fallback_span
                        .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                ));
            }
        }
    }

    for iface_query in &interface.queries {
        match target
            .queries
            .iter()
            .find(|query| query.name == iface_query.name)
        {
            Some(implemented_query) => {
                if implemented_query.params.len() != iface_query.params.len() {
                    errors.push(ElabError::with_span(
                        ErrorKind::ParamMismatch,
                        format!(
                            "{} `{}` query `{}` has {} parameter(s), but interface `{}` requires {}",
                            target.decl_kind,
                            target.decl_name,
                            iface_query.name,
                            implemented_query.params.len(),
                            interface.name,
                            iface_query.params.len()
                        ),
                        target.ctx,
                        implemented_query
                            .span
                            .or(target.fallback_span)
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                } else {
                    for (idx, (implemented_param, iface_param)) in implemented_query
                        .params
                        .iter()
                        .zip(iface_query.params.iter())
                        .enumerate()
                    {
                        if !types_compatible_in_env(env, &implemented_param.1, &iface_param.1) {
                            errors.push(ElabError::with_span(
                                ErrorKind::TypeMismatch,
                                format!(
                                    "{} `{}` query `{}` parameter {} has type `{}` but interface `{}` requires `{}`",
                                    target.decl_kind,
                                    target.decl_name,
                                    iface_query.name,
                                    idx + 1,
                                    implemented_param.1.name(),
                                    interface.name,
                                    iface_param.1.name()
                                ),
                                target.ctx,
                                implemented_query
                                    .span
                                    .or(target.fallback_span)
                                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                            ));
                        }
                    }
                }

                let implemented_ret = &implemented_query.return_type;
                let iface_ret = &iface_query.return_type;
                if !matches!(implemented_ret, Ty::Error)
                    && !matches!(iface_ret, Ty::Error)
                    && !types_compatible_in_env(env, implemented_ret, iface_ret)
                {
                    errors.push(ElabError::with_span(
                        ErrorKind::TypeMismatch,
                        format!(
                            "{} `{}` query `{}` returns `{}` but interface `{}` requires `{}`",
                            target.decl_kind,
                            target.decl_name,
                            iface_query.name,
                            implemented_ret.name(),
                            interface.name,
                            iface_ret.name()
                        ),
                        target.ctx,
                        implemented_query
                            .span
                            .or(target.fallback_span)
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                }
            }
            None => {
                errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "{} `{}` is missing query `{}` required by interface `{}`",
                        target.decl_kind, target.decl_name, iface_query.name, interface.name
                    ),
                    target.ctx,
                    target
                        .fallback_span
                        .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                ));
            }
        }
    }

    true
}

pub(super) fn check_extern(env: &Env, ext: &EExtern) -> Vec<ElabError> {
    let mut errors = Vec::new();
    let ext_ctx = format!("extern {}", ext.name);

    if !check_interface_conformance(
        env,
        InterfaceConformanceTarget {
            decl_kind: "extern",
            decl_name: &ext.name,
            implements: ext.implements.as_deref(),
            commands: &ext.commands,
            queries: &[],
            ctx: &ext_ctx,
            fallback_span: ext.span,
        },
        &mut errors,
    ) {
        return errors;
    }

    let command_map: HashMap<&str, _> = ext.commands.iter().map(|c| (c.name.as_str(), c)).collect();
    let mut seen_may: HashSet<&str> = HashSet::new();

    for may in &ext.mays {
        let Some(command) = command_map.get(may.command.as_str()) else {
            errors.push(ElabError::with_span(
                ErrorKind::UndefinedRef,
                format!(
                    "extern `{}` has `may {}` for unknown command `{}`",
                    ext.name, may.command, may.command
                ),
                &ext_ctx,
                may.span
                    .or(ext.span)
                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
            ));
            continue;
        };

        if !seen_may.insert(may.command.as_str()) {
            errors.push(ElabError::with_span(
                ErrorKind::DuplicateDecl,
                format!(
                    "extern `{}` declares multiple `may {}` blocks for command `{}`",
                    ext.name, may.command, may.command
                ),
                &ext_ctx,
                may.span
                    .or(ext.span)
                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
            ));
        }

        match &command.return_type {
            Some(return_ty) => {
                for ret in &may.returns {
                    let ret_ty = ret.ty();
                    if !matches!(ret_ty, Ty::Error)
                        && !types_compatible_in_env(env, &ret_ty, return_ty)
                    {
                        errors.push(ElabError::with_span(
                            ErrorKind::TypeMismatch,
                            format!(
                                "extern `{}` `may {}` returns `{}` but command `{}` requires `{}`",
                                ext.name,
                                may.command,
                                ret_ty.name(),
                                may.command,
                                return_ty.name()
                            ),
                            &ext_ctx,
                            may.span
                                .or(ext.span)
                                .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    }
                }
            }
            None => {
                if !may.returns.is_empty() {
                    errors.push(ElabError::with_span(
                        ErrorKind::TypeMismatch,
                        format!(
                            "extern `{}` command `{}` has no return type but `may {}` returns values",
                            ext.name, may.command, may.command
                        ),
                        &ext_ctx,
                        may.span.or(ext.span).unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                }
            }
        }
    }

    for command in &ext.commands {
        if !seen_may.contains(command.name.as_str()) {
            errors.push(ElabError::with_span(
                ErrorKind::MissingField,
                format!(
                    "extern `{}` command `{}` is missing a `may {}` block",
                    ext.name, command.name, command.name
                ),
                &ext_ctx,
                command
                    .span
                    .or(ext.span)
                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
            ));
        }
    }

    for assume in &ext.assumes {
        match assume {
            EExternAssume::Fair(path, span) | EExternAssume::StrongFair(path, span) => {
                if path.len() != 1 {
                    errors.push(ElabError::with_span(
                        ErrorKind::UndefinedRef,
                        format!(
                            "extern `{}` fairness assumptions must reference a local command name",
                            ext.name
                        ),
                        &ext_ctx,
                        span.or(ext.span)
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                    continue;
                }
                let command = &path[0];
                if !command_map.contains_key(command.as_str()) {
                    errors.push(ElabError::with_span(
                        ErrorKind::UndefinedRef,
                        format!(
                            "extern `{}` fairness assumption references unknown command `{command}`",
                            ext.name
                        ),
                        &ext_ctx,
                        span.or(ext.span).unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                }
            }
            EExternAssume::Expr(expr, _) => {
                if !matches!(
                    expr.ty(),
                    Ty::Builtin(super::super::types::BuiltinTy::Bool) | Ty::Error
                ) {
                    errors.push(ElabError::with_span(
                        ErrorKind::TypeMismatch,
                        format!("extern `{}` assume expression must be bool", ext.name),
                        &ext_ctx,
                        expr_span(expr)
                            .unwrap_or(ext.span.unwrap_or(crate::span::Span { start: 0, end: 0 })),
                    ));
                }
            }
        }
    }

    errors
}

struct CrossCallValidationCtx<'a> {
    env: &'a Env,
    system_name: &'a str,
    sys_ctx: &'a str,
    deps: &'a [String],
    fallback_span: Option<crate::span::Span>,
}

fn validate_crosscalls_in_actions(
    ctx: &CrossCallValidationCtx<'_>,
    actions: &[EEventAction],
    errors: &mut Vec<ElabError>,
    local_return_types: &mut HashMap<String, Ty>,
) {
    for action in actions {
        match action {
            EEventAction::Choose(_, _, _, body) | EEventAction::ForAll(_, _, body) => {
                let mut scoped_return_types = local_return_types.clone();
                validate_crosscalls_in_actions(ctx, body, errors, &mut scoped_return_types);
            }
            EEventAction::LetCrossCall(name, target, command, args) => {
                validate_crosscall_target(ctx, target, command, args, errors);
                if let Some(return_type) = command_return_type(ctx.env, target, command) {
                    local_return_types.insert(name.clone(), return_type.clone());
                }
            }
            EEventAction::CrossCall(target, command, args) => {
                validate_crosscall_target(ctx, target, command, args, errors);
            }
            EEventAction::Match(scrutinee, arms) => {
                let scrutinee_ty = match scrutinee {
                    EMatchScrutinee::Var(name) => local_return_types.get(name),
                    EMatchScrutinee::CrossCall(target, command, _) => {
                        command_return_type(ctx.env, target, command)
                    }
                };
                if let Some(ty) = scrutinee_ty {
                    if let Some((enum_name, constructors)) =
                        resolve_to_enum_info(ty, &ctx.env.types)
                    {
                        for arm in arms {
                            check_pattern_shape(
                                &arm.pattern,
                                enum_name,
                                constructors,
                                &ctx.env.variant_fields,
                                ctx.fallback_span
                                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                                errors,
                            );
                        }
                    }
                }
                if let EMatchScrutinee::CrossCall(target, command, args) = scrutinee {
                    validate_crosscall_target(ctx, target, command, args, errors);
                }
                for arm in arms {
                    let mut scoped_return_types = local_return_types.clone();
                    validate_crosscalls_in_actions(
                        ctx,
                        &arm.body,
                        errors,
                        &mut scoped_return_types,
                    );
                }
            }
            EEventAction::Create(_, _, _)
            | EEventAction::Apply(_, _, _, _)
            | EEventAction::Expr(_) => {}
        }
    }
}

fn command_return_type<'a>(env: &'a Env, target: &str, command: &str) -> Option<&'a Ty> {
    if let Some(system) = env.systems.get(target) {
        return system
            .commands
            .iter()
            .find(|candidate| candidate.name == command)
            .and_then(|candidate| candidate.return_type.as_ref());
    }
    env.externs.get(target).and_then(|ext| {
        ext.commands
            .iter()
            .find(|candidate| candidate.name == command)
            .and_then(|candidate| candidate.return_type.as_ref())
    })
}

fn validate_crosscall_target(
    ctx: &CrossCallValidationCtx<'_>,
    target: &str,
    command: &str,
    args: &[EExpr],
    errors: &mut Vec<ElabError>,
) {
    let is_system = ctx.env.systems.contains_key(target);
    let is_extern = ctx.env.externs.contains_key(target);
    let span = ctx
        .fallback_span
        .unwrap_or(crate::span::Span { start: 0, end: 0 });

    if is_system && is_extern {
        errors.push(ElabError::with_span(
            ErrorKind::AmbiguousRef,
            format!("cross-call target `{target}` is ambiguous between a system and an extern"),
            ctx.sys_ctx,
            span,
        ));
        return;
    }

    if is_extern {
        if !ctx.deps.iter().any(|dep| dep == target) {
            errors.push(ElabError::with_span(
                ErrorKind::InvalidScope,
                format!(
                    "system `{}` calls extern `{target}` without declaring `dep {target}`",
                    ctx.system_name
                ),
                ctx.sys_ctx,
                span,
            ));
            return;
        }

        if let Some(ext) = ctx.env.externs.get(target) {
            match ext.commands.iter().find(|c| c.name == command) {
                Some(cmd) => {
                    if cmd.params.len() != args.len() {
                        errors.push(ElabError::with_span(
                            ErrorKind::ParamMismatch,
                            format!(
                                "extern call `{target}::{command}` expects {} args but got {}",
                                cmd.params.len(),
                                args.len()
                            ),
                            ctx.sys_ctx,
                            span,
                        ));
                    }
                }
                None => errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!("extern `{target}` has no command `{command}`"),
                    ctx.sys_ctx,
                    span,
                )),
            }
        }
    } else if is_system {
        if let Some(target_sys) = ctx.env.systems.get(target) {
            if let Some(cmd) = target_sys.commands.iter().find(|cmd| cmd.name == *command) {
                if cmd.params.len() != args.len() {
                    errors.push(ElabError::with_span(
                        ErrorKind::ParamMismatch,
                        format!(
                            "cross-call `{target}::{command}` expects {} args but got {}",
                            cmd.params.len(),
                            args.len()
                        ),
                        ctx.sys_ctx,
                        span,
                    ));
                }
            } else {
                errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!("system `{target}` has no command `{command}`"),
                    ctx.sys_ctx,
                    span,
                ));
            }
        }
    } else {
        errors.push(ElabError::with_span(
            ErrorKind::UndefinedRef,
            format!("cross-call target `{target}` is not a known system or extern"),
            ctx.sys_ctx,
            span,
        ));
    }
}

fn expr_span(expr: &EExpr) -> Option<crate::span::Span> {
    match expr {
        EExpr::Lit(_, _, span)
        | EExpr::Var(_, _, span)
        | EExpr::Prime(_, _, span)
        | EExpr::Always(_, _, span)
        | EExpr::Eventually(_, _, span)
        | EExpr::Historically(_, _, span)
        | EExpr::Once(_, _, span)
        | EExpr::Previously(_, _, span)
        | EExpr::Assert(_, _, span)
        | EExpr::Assume(_, _, span)
        | EExpr::Match(_, _, span)
        | EExpr::Choose(_, _, _, _, span)
        | EExpr::TupleLit(_, _, span)
        | EExpr::SetLit(_, _, span)
        | EExpr::SeqLit(_, _, span)
        | EExpr::MapLit(_, _, span)
        | EExpr::Sorry(span)
        | EExpr::Todo(span)
        | EExpr::Block(_, span)
        | EExpr::StructCtor(_, _, _, span) => *span,
        EExpr::Field(_, _, _, span)
        | EExpr::BinOp(_, _, _, _, span)
        | EExpr::UnOp(_, _, _, span)
        | EExpr::Call(_, _, _, span)
        | EExpr::CallR(_, _, _, _, span)
        | EExpr::Qual(_, _, _, span)
        | EExpr::Quant(_, _, _, _, _, span)
        | EExpr::Let(_, _, span)
        | EExpr::Until(_, _, _, span)
        | EExpr::Since(_, _, _, span)
        | EExpr::Assign(_, _, _, span)
        | EExpr::NamedPair(_, _, _, span)
        | EExpr::Seq(_, _, _, span)
        | EExpr::SameStep(_, _, _, span)
        | EExpr::IfElse(_, _, _, span)
        | EExpr::In(_, _, _, span)
        | EExpr::Card(_, _, span)
        | EExpr::Pipe(_, _, _, span)
        | EExpr::MapUpdate(_, _, _, _, span)
        | EExpr::Index(_, _, _, span)
        | EExpr::SetComp(_, _, _, _, _, _, span)
        | EExpr::RelComp(_, _, _, _, span)
        | EExpr::QualCall(_, _, _, _, span)
        | EExpr::Lam(_, _, _, span)
        | EExpr::VarDecl(_, _, _, _, span)
        | EExpr::While(_, _, _, span)
        | EExpr::Aggregate(_, _, _, _, _, _, span)
        | EExpr::Saw(_, _, _, _, span)
        | EExpr::CtorRecord(_, _, _, _, span)
        | EExpr::Unresolved(_, span) => *span,
    }
}

/// Extract the constructor name from a return expression.
///
/// Handles common forms:
/// - `@ok` → `Var(Ty::Enum(..), "ok")` → Some("ok")
/// - `@ok(42)` → `Call(_, Var(_, "ok"), [42])` → Some("ok")
/// - `@ok(Receipt {... })` → `Call(_, Var(_, "ok"), [StructCtor(...)])` → Some("ok")
pub(super) fn extract_return_ctor_name(expr: &EExpr) -> Option<String> {
    match expr {
        // Bare constructor: @ok
        EExpr::Var(_, name, _) => Some(name.clone()),
        // Constructor with args: @ok(42), @ok(Receipt {... })
        EExpr::Call(_, callee, _, _) => {
            if let EExpr::Var(_, name, _) = callee.as_ref() {
                Some(name.clone())
            } else {
                None
            }
        }
        // CtorRecord: @ok { field: val }
        EExpr::CtorRecord(_, _, name, _, _) => Some(name.clone()),
        _ => None,
    }
}

/// Payload form: positional (tuple variant) or named (record variant).
pub(super) enum ReturnPayload<'a> {
    /// Positional args: `@ok(42)`, `@ok(1, 2)`, or bare `@ok`
    Positional(Vec<&'a EExpr>),
    /// Named fields: `@ok { a: 1, b: true }`
    Named(Vec<(&'a str, &'a EExpr)>),
}

/// Extract the payload from a return expression.
pub(super) fn extract_return_payload(expr: &EExpr) -> ReturnPayload<'_> {
    match expr {
        EExpr::Call(_, _, args, _) => ReturnPayload::Positional(args.iter().collect()),
        EExpr::CtorRecord(_, _, _, fields, _) => {
            ReturnPayload::Named(fields.iter().map(|(n, e)| (n.as_str(), e)).collect())
        }
        _ => ReturnPayload::Positional(vec![]),
    }
}

struct ProcDepCheckCtx<'a> {
    env: &'a Env,
    proc: &'a super::super::types::EProc,
    node_names: &'a HashSet<&'a str>,
    let_binding_systems: &'a HashMap<&'a str, &'a str>,
    proc_ctx: &'a str,
    span: crate::span::Span,
}

fn validate_proc_dep_cond(
    ctx: &ProcDepCheckCtx<'_>,
    cond: &EProcDepCond,
    errors: &mut Vec<ElabError>,
) {
    match cond {
        EProcDepCond::Fact { node, qualifier } => {
            if !ctx.node_names.contains(node.as_str()) {
                errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "needs condition references source `{node}` which is not a declared node in proc `{}`",
                        ctx.proc.name
                    ),
                    ctx.proc_ctx,
                    ctx.span,
                ));
                return;
            }
            match qualifier.as_deref() {
                None | Some("done") => {}
                Some(port) => {
                    let source_node = ctx.proc.nodes.iter().find(|n| n.name == *node);
                    if let Some(node) = source_node {
                        if let Some(sys_type) = ctx.let_binding_systems.get(node.instance.as_str())
                        {
                            if let Some(bound_sys) = ctx.env.systems.get(*sys_type) {
                                if let Some(cmd) =
                                    bound_sys.commands.iter().find(|c| c.name == node.command)
                                {
                                    match &cmd.return_type {
                                        None => {
                                            errors.push(ElabError::with_span(
                                                ErrorKind::TypeMismatch,
                                                format!(
                                                    "needs condition references port `.{port}` on `{}` but command `{}` has no return type",
                                                    node.name, node.command
                                                ),
                                                ctx.proc_ctx,
                                                ctx.span,
                                            ));
                                        }
                                        Some(Ty::Enum(_, variants)) => {
                                            if !variants.iter().any(|v| v == port) {
                                                errors.push(ElabError::with_span(
                                                    ErrorKind::UndefinedRef,
                                                    format!(
                                                        "needs condition references port `.{port}` but command `{}` return type has variants: {}",
                                                        node.command,
                                                        variants
                                                            .iter()
                                                            .map(|v| format!(".{v}"))
                                                            .collect::<Vec<_>>()
                                                            .join(", ")
                                                    ),
                                                    ctx.proc_ctx,
                                                    ctx.span,
                                                ));
                                            }
                                        }
                                        Some(other_ty) => {
                                            errors.push(ElabError::with_span(
                                                ErrorKind::TypeMismatch,
                                                format!(
                                                    "needs condition references port `.{port}` on `{}` but command `{}` returns `{}`, not an enum; outcome ports require an enum return type",
                                                    node.name, node.command, other_ty.name()
                                                ),
                                                ctx.proc_ctx,
                                                ctx.span,
                                            ));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        EProcDepCond::Not(inner) => {
            validate_proc_dep_cond(ctx, inner, errors);
        }
        EProcDepCond::And(left, right) | EProcDepCond::Or(left, right) => {
            validate_proc_dep_cond(ctx, left, errors);
            validate_proc_dep_cond(ctx, right, errors);
        }
    }
}

fn collect_proc_dep_sources<'a>(cond: &'a EProcDepCond, out: &mut Vec<&'a str>) {
    match cond {
        EProcDepCond::Fact { node, .. } => out.push(node.as_str()),
        EProcDepCond::Not(inner) => collect_proc_dep_sources(inner, out),
        EProcDepCond::And(left, right) | EProcDepCond::Or(left, right) => {
            collect_proc_dep_sources(left, out);
            collect_proc_dep_sources(right, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::types::{
        BuiltinTy, ECommand, EEntity, EField, EFieldDefault, EInterface, EMay, EProc, EProcEdge,
        EProcNode, EQuery, EQuerySig, EScope, EStoreParam, ESystemAction, Literal,
    };
    use super::*;

    fn ty_string() -> Ty {
        Ty::Builtin(BuiltinTy::String)
    }

    fn ty_int() -> Ty {
        Ty::Builtin(BuiltinTy::Int)
    }

    fn payment_decision_ty() -> Ty {
        Ty::Enum(
            "PaymentDecision".to_owned(),
            vec!["Approved".to_owned(), "Declined".to_owned()],
        )
    }

    fn command(name: &str, return_type: Option<Ty>) -> ECommand {
        ECommand {
            name: name.to_owned(),
            params: vec![("amount".to_owned(), ty_int())],
            return_type,
            span: None,
        }
    }

    fn may(name: &str, literal: EExpr) -> EMay {
        EMay {
            command: name.to_owned(),
            returns: vec![literal],
            span: None,
        }
    }

    fn lit_string(value: &str) -> EExpr {
        EExpr::Lit(ty_string(), Literal::Str(value.to_owned()), None)
    }

    fn lit_int(value: i64) -> EExpr {
        EExpr::Lit(ty_int(), Literal::Int(value), None)
    }

    fn enum_variant(ty: Ty, variant: &str) -> EExpr {
        EExpr::Var(ty, variant.to_owned(), None)
    }

    fn env_with_interface(interface: EInterface) -> Env {
        let mut env = Env::new();
        env.interfaces.insert(interface.name.clone(), interface);
        env
    }

    fn payment_interface() -> EInterface {
        EInterface {
            name: "PaymentProcessor".to_owned(),
            commands: vec![command("authorize", Some(ty_string()))],
            queries: vec![],
            span: None,
        }
    }

    fn system_with_command(name: &str, return_type: Option<Ty>) -> ESystem {
        ESystem {
            name: "Payments".to_string(),
            implements: None,
            deps: vec![],
            fields: vec![],
            store_params: vec![],
            scopes: vec![],
            commands: vec![ECommand {
                name: name.to_string(),
                params: vec![],
                return_type,
                span: None,
            }],
            actions: vec![],
            queries: vec![],
            fsm_decls: vec![],
            derived_fields: vec![],
            invariants: vec![],
            preds: vec![],
            let_bindings: vec![],
            procs: vec![],
            proc_uses: vec![],
            span: None,
        }
    }

    fn query(name: &str, params: Vec<(String, Ty)>, body: EExpr) -> EQuery {
        EQuery {
            name: name.to_string(),
            params,
            body,
            span: None,
        }
    }

    fn entity(name: &str) -> EEntity {
        EEntity {
            name: name.to_string(),
            fields: vec![],
            actions: vec![],
            derived_fields: vec![],
            invariants: vec![],
            fsm_decls: vec![],
            span: None,
        }
    }

    fn store_param(name: &str, entity_type: &str, lo: Option<i64>, hi: Option<i64>) -> EStoreParam {
        EStoreParam {
            name: name.to_string(),
            entity_type: entity_type.to_string(),
            lo,
            hi,
        }
    }

    fn scope(entity: &str, lo: i64, hi: i64) -> EScope {
        EScope {
            entity: entity.to_string(),
            lo,
            hi,
        }
    }

    fn system_field(name: &str, ty: Ty, default: Option<EFieldDefault>) -> EField {
        EField {
            name: name.to_string(),
            ty,
            default,
            span: None,
        }
    }

    fn system_action(name: &str, return_expr: Option<EExpr>) -> ESystemAction {
        ESystemAction {
            name: name.to_string(),
            params: vec![],
            requires: vec![],
            body: vec![],
            return_expr,
            span: Some(crate::span::Span { start: 7, end: 8 }),
        }
    }

    fn proc_with_node(command: &str) -> EProc {
        EProc {
            name: "checkout".to_string(),
            params: vec![],
            requires: None,
            nodes: vec![EProcNode {
                name: "charge".to_string(),
                instance: "payments".to_string(),
                command: command.to_string(),
                args: vec![],
            }],
            edges: vec![],
            proc_uses: vec![],
            span: None,
        }
    }

    #[test]
    fn system_checker_validates_store_entities_and_bounds() {
        let mut env = Env::new();
        env.entities
            .insert("Commerce::Ticket".to_string(), entity("Ticket"));
        env.entities.insert("Order".to_string(), entity("Order"));

        let mut system = system_with_command("noop", None);
        system.store_params = vec![
            store_param("tickets", "Ticket", Some(0), Some(1)),
            store_param("orders", "Order", Some(0), Some(0)),
        ];
        assert!(
            check_system(&env, &system).is_empty(),
            "canonical and direct entity store params with valid bounds should pass"
        );

        system.store_params = vec![
            store_param("missing", "Missing", Some(0), Some(1)),
            store_param("negative_lo", "Order", Some(-1), Some(1)),
            store_param("negative_hi", "Order", Some(0), Some(-1)),
            store_param("reversed", "Order", Some(2), Some(1)),
        ];
        let errors = check_system(&env, &system);
        assert_eq!(errors.len(), 4);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("unknown entity 'Missing'")));
        assert_eq!(
            errors
                .iter()
                .filter(|error| error.message.contains("invalid bounds"))
                .count(),
            3
        );
    }

    #[test]
    fn system_checker_validates_deps_interface_scopes_and_struct_defaults() {
        let mut env = Env::new();
        env.externs.insert(
            "StripeGateway".to_string(),
            EExtern {
                name: "StripeGateway".to_string(),
                implements: None,
                commands: vec![],
                mays: vec![],
                assumes: vec![],
                span: None,
            },
        );
        let mut system = system_with_command("noop", None);
        system.deps = vec![
            "StripeGateway".to_string(),
            "StripeGateway".to_string(),
            "MissingGateway".to_string(),
        ];
        system.scopes = vec![
            scope("Ticket", 0, 1),
            scope("Ticket", -1, 1),
            scope("Ticket", 2, 1),
        ];
        system.fields = vec![system_field(
            "config",
            Ty::Record(
                "Config".to_string(),
                vec![
                    ("host".to_string(), ty_string()),
                    ("retries".to_string(), ty_int()),
                ],
            ),
            Some(EFieldDefault::Value(EExpr::StructCtor(
                Ty::Error,
                "Config".to_string(),
                vec![
                    ("host".to_string(), lit_string("localhost")),
                    ("host".to_string(), lit_string("duplicate")),
                    ("extra".to_string(), lit_int(1)),
                ],
                Some(crate::span::Span { start: 9, end: 10 }),
            ))),
        )];

        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("duplicate dep `StripeGateway`")));
        assert!(errors.iter().any(|error| error
            .message
            .contains("unknown extern dep `MissingGateway`")));
        assert_eq!(
            errors
                .iter()
                .filter(|error| error.message.contains("invalid range"))
                .count(),
            2
        );
        assert!(errors
            .iter()
            .any(|error| error.message.contains("unknown field `extra`")));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("duplicate field `host`")));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("missing field `retries`")));

        let mut missing_interface_system = system_with_command("noop", None);
        missing_interface_system.implements = Some("MissingInterface".to_string());
        missing_interface_system.scopes = vec![scope("Ticket", -1, 1)];
        let errors = check_system(&Env::new(), &missing_interface_system);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("unknown interface"));

        let mut valid_system = system_with_command("noop", None);
        valid_system.deps = vec!["StripeGateway".to_string()];
        valid_system.scopes = vec![scope("Ticket", 0, 1), scope("Ticket", 0, 0)];
        valid_system.fields = vec![system_field(
            "config",
            Ty::Record(
                "Config".to_string(),
                vec![
                    ("host".to_string(), ty_string()),
                    ("retries".to_string(), ty_int()),
                ],
            ),
            Some(EFieldDefault::Value(EExpr::StructCtor(
                Ty::Error,
                "Config".to_string(),
                vec![
                    ("host".to_string(), lit_string("localhost")),
                    ("retries".to_string(), lit_int(3)),
                ],
                None,
            ))),
        )];
        assert!(
            check_system(&env, &valid_system).is_empty(),
            "unique deps, valid scopes, and complete struct defaults should pass"
        );
    }

    #[test]
    fn system_checker_validates_command_return_expressions() {
        let outcome_ty = Ty::Enum(
            "Outcome".to_string(),
            vec!["Ok".to_string(), "Err".to_string(), "Poison".to_string()],
        );
        let mut env = Env::new();
        env.variant_fields.insert(
            "Outcome".to_string(),
            vec![
                ("Ok".to_string(), vec![]),
                ("Err".to_string(), vec![("code".to_string(), ty_int())]),
                ("Poison".to_string(), vec![("value".to_string(), Ty::Error)]),
            ],
        );

        let mut system = system_with_command("authorize", None);
        system.actions = vec![system_action(
            "authorize",
            Some(EExpr::Var(outcome_ty.clone(), "Ok".to_string(), None)),
        )];
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("does not declare a return type")));

        system = system_with_command("authorize", Some(outcome_ty.clone()));
        system.actions = vec![system_action(
            "authorize",
            Some(EExpr::Var(outcome_ty.clone(), "Ok".to_string(), None)),
        )];
        assert!(
            check_system(&env, &system).is_empty(),
            "valid enum return constructor should pass"
        );

        system.actions = vec![system_action(
            "authorize",
            Some(EExpr::CtorRecord(
                outcome_ty,
                Some("Outcome".to_string()),
                "Err".to_string(),
                vec![("code".to_string(), lit_int(1))],
                None,
            )),
        )];
        assert!(
            check_system(&env, &system).is_empty(),
            "valid enum record return constructor should pass"
        );

        system.actions = vec![system_action(
            "authorize",
            Some(EExpr::Var(
                Ty::Enum(
                    "Outcome".to_string(),
                    vec!["Ok".to_string(), "Err".to_string()],
                ),
                "Missing".to_string(),
                None,
            )),
        )];
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("not a variant")));

        let outcome_ty = Ty::Enum(
            "Outcome".to_string(),
            vec!["Ok".to_string(), "Err".to_string()],
        );
        system.actions = vec![system_action(
            "authorize",
            Some(EExpr::Call(
                outcome_ty.clone(),
                Box::new(EExpr::Var(outcome_ty.clone(), "Err".to_string(), None)),
                vec![lit_string("wrong")],
                None,
            )),
        )];
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("with argument 1")));

        system.actions = vec![system_action(
            "authorize",
            Some(EExpr::Call(
                outcome_ty.clone(),
                Box::new(EExpr::Var(outcome_ty.clone(), "Err".to_string(), None)),
                vec![lit_int(1)],
                None,
            )),
        )];
        assert!(
            !check_system(&env, &system)
                .iter()
                .any(|error| error.message.contains("with argument 1")),
            "valid positional payload types should not produce return payload diagnostics"
        );

        system.actions = vec![system_action(
            "authorize",
            Some(EExpr::Call(
                Ty::Enum(
                    "Outcome".to_string(),
                    vec!["Ok".to_string(), "Err".to_string(), "Poison".to_string()],
                ),
                Box::new(EExpr::Var(
                    Ty::Enum(
                        "Outcome".to_string(),
                        vec!["Ok".to_string(), "Err".to_string(), "Poison".to_string()],
                    ),
                    "Err".to_string(),
                    None,
                )),
                vec![EExpr::Var(Ty::Error, "unknown".to_string(), None)],
                None,
            )),
        )];
        assert!(
            !check_system(&env, &system)
                .iter()
                .any(|error| error.message.contains("with argument 1")),
            "poison argument types should not produce return payload type diagnostics"
        );

        system.actions = vec![system_action(
            "authorize",
            Some(EExpr::Call(
                Ty::Enum(
                    "Outcome".to_string(),
                    vec!["Ok".to_string(), "Err".to_string(), "Poison".to_string()],
                ),
                Box::new(EExpr::Var(
                    Ty::Enum(
                        "Outcome".to_string(),
                        vec!["Ok".to_string(), "Err".to_string(), "Poison".to_string()],
                    ),
                    "Poison".to_string(),
                    None,
                )),
                vec![lit_string("anything")],
                None,
            )),
        )];
        assert!(
            !check_system(&env, &system)
                .iter()
                .any(|error| error.message.contains("with argument 1")),
            "poison declared payload types should not produce return payload type diagnostics"
        );

        system.actions = vec![system_action(
            "authorize",
            Some(EExpr::CtorRecord(
                outcome_ty,
                Some("Outcome".to_string()),
                "Err".to_string(),
                vec![("code".to_string(), lit_string("wrong"))],
                None,
            )),
        )];
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("with field")));

        system = system_with_command("authorize", Some(ty_int()));
        system.actions = vec![system_action("authorize", Some(lit_int(1)))];
        assert!(
            check_system(&env, &system).is_empty(),
            "non-enum return types are accepted for now"
        );
    }

    #[test]
    fn system_checker_validates_proc_requires_are_boolean() {
        let env = Env::new();
        let mut system = system_with_command("noop", None);
        let mut proc = proc_with_node("noop");
        proc.requires = Some(lit_int(1));
        system.procs = vec![proc];

        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message == crate::messages::MSG_REQUIRES_SHOULD_BE_BOOL));

        let mut valid_proc = proc_with_node("noop");
        valid_proc.requires = Some(EExpr::Lit(
            Ty::Builtin(BuiltinTy::Bool),
            Literal::Bool(true),
            None,
        ));
        system.procs = vec![valid_proc];
        let errors = check_system(&env, &system);
        assert!(
            !errors
                .iter()
                .any(|error| error.message == crate::messages::MSG_REQUIRES_SHOULD_BE_BOOL),
            "bool proc requires should not produce requires-type diagnostics"
        );
        assert!(
            !errors
                .iter()
                .any(|error| error.message.contains("duplicate proc node")),
            "single proc node should not be reported as duplicate"
        );

        let mut duplicate_proc = proc_with_node("noop");
        duplicate_proc.nodes.push(EProcNode {
            name: "charge".to_string(),
            instance: "payments".to_string(),
            command: "noop".to_string(),
            args: vec![],
        });
        system.procs = vec![duplicate_proc];
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("duplicate proc node `charge`")));
    }

    #[test]
    fn system_checker_validates_proc_nodes_edges_and_cycles() {
        let mut env = Env::new();
        let mut bound_system = system_with_command("charge", None);
        bound_system.commands[0].params = vec![("amount".to_string(), ty_int())];
        env.systems
            .insert("Payments".to_string(), bound_system.clone());

        let mut system = bound_system;
        let valid_node = EProcNode {
            name: "charge".to_string(),
            instance: "self".to_string(),
            command: "charge".to_string(),
            args: vec![lit_int(1)],
        };
        let valid_proc = EProc {
            name: "checkout".to_string(),
            params: vec![],
            requires: None,
            nodes: vec![valid_node.clone()],
            edges: vec![],
            proc_uses: vec![],
            span: None,
        };
        system.procs = vec![valid_proc];
        assert!(
            check_system(&env, &system).is_empty(),
            "valid proc node arguments and acyclic empty graph should pass"
        );

        let bad_type_proc = EProc {
            name: "checkout".to_string(),
            params: vec![],
            requires: None,
            nodes: vec![EProcNode {
                args: vec![lit_string("wrong")],
                ..valid_node.clone()
            }],
            edges: vec![],
            proc_uses: vec![],
            span: None,
        };
        system.procs = vec![bad_type_proc];
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("passes argument 1")));

        let poison_arg_proc = EProc {
            name: "checkout".to_string(),
            params: vec![],
            requires: None,
            nodes: vec![EProcNode {
                args: vec![EExpr::Var(Ty::Error, "unknown".to_string(), None)],
                ..valid_node.clone()
            }],
            edges: vec![],
            proc_uses: vec![],
            span: None,
        };
        system.procs = vec![poison_arg_proc];
        assert!(
            !check_system(&env, &system)
                .iter()
                .any(|error| error.message.contains("passes argument 1")),
            "poison proc node args should not produce type diagnostics"
        );

        let arity_proc = EProc {
            name: "checkout".to_string(),
            params: vec![],
            requires: None,
            nodes: vec![EProcNode {
                args: vec![],
                ..valid_node.clone()
            }],
            edges: vec![],
            proc_uses: vec![],
            span: None,
        };
        system.procs = vec![arity_proc];
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("passes 0 argument(s)")));

        let unknown_edge_proc = EProc {
            name: "checkout".to_string(),
            params: vec![],
            requires: None,
            nodes: vec![valid_node.clone()],
            edges: vec![EProcEdge {
                target: "missing".to_string(),
                condition: EProcDepCond::Fact {
                    node: "charge".to_string(),
                    qualifier: None,
                },
            }],
            proc_uses: vec![],
            span: None,
        };
        system.procs = vec![unknown_edge_proc];
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("edge target `missing`")));

        let cyclic_proc = EProc {
            name: "checkout".to_string(),
            params: vec![],
            requires: None,
            nodes: vec![
                valid_node.clone(),
                EProcNode {
                    name: "settle".to_string(),
                    instance: "self".to_string(),
                    command: "charge".to_string(),
                    args: vec![lit_int(1)],
                },
            ],
            edges: vec![
                EProcEdge {
                    target: "settle".to_string(),
                    condition: EProcDepCond::Fact {
                        node: "charge".to_string(),
                        qualifier: None,
                    },
                },
                EProcEdge {
                    target: "charge".to_string(),
                    condition: EProcDepCond::Fact {
                        node: "settle".to_string(),
                        qualifier: None,
                    },
                },
            ],
            proc_uses: vec![],
            span: None,
        };
        system.procs = vec![cyclic_proc];
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("dependency cycle")));
    }

    #[test]
    fn check_extern_rejects_missing_interface_command() {
        let env = env_with_interface(payment_interface());
        let ext = EExtern {
            name: "StripeGateway".to_owned(),
            implements: Some("PaymentProcessor".to_owned()),
            commands: vec![command("capture", Some(ty_string()))],
            mays: vec![may("capture", lit_string("ok"))],
            assumes: vec![],
            span: None,
        };

        let errors = check_extern(&env, &ext);

        assert!(
            errors.iter().any(|error| error.message.contains(
                "extern `StripeGateway` is missing command `authorize` required by interface `PaymentProcessor`"
            )),
            "expected missing extern command diagnostic, got: {errors:?}"
        );
    }

    #[test]
    fn check_extern_rejects_interface_command_return_mismatch() {
        let env = env_with_interface(payment_interface());
        let ext = EExtern {
            name: "StripeGateway".to_owned(),
            implements: Some("PaymentProcessor".to_owned()),
            commands: vec![command("authorize", Some(ty_int()))],
            mays: vec![may("authorize", lit_int(1))],
            assumes: vec![],
            span: None,
        };

        let errors = check_extern(&env, &ext);

        assert!(
            errors.iter().any(|error| error.message.contains(
                "extern `StripeGateway` command `authorize` returns `int` but interface `PaymentProcessor` requires `string`"
            )),
            "expected extern command return mismatch diagnostic, got: {errors:?}"
        );
    }

    #[test]
    fn check_extern_accepts_named_enum_interface_command_return() {
        let enum_ty = payment_decision_ty();
        let interface = EInterface {
            name: "PaymentProcessor".to_owned(),
            commands: vec![command(
                "authorize",
                Some(Ty::Named("PaymentDecision".to_owned())),
            )],
            queries: vec![],
            span: None,
        };
        let mut env = env_with_interface(interface);
        env.types
            .insert("PaymentDecision".to_owned(), enum_ty.clone());
        let ext = EExtern {
            name: "StripeGateway".to_owned(),
            implements: Some("PaymentProcessor".to_owned()),
            commands: vec![command("authorize", Some(enum_ty.clone()))],
            mays: vec![may("authorize", enum_variant(enum_ty, "Approved"))],
            assumes: vec![],
            span: None,
        };

        let errors = check_extern(&env, &ext);

        assert!(
            errors.is_empty(),
            "expected compatible enum return conformance, got: {errors:?}"
        );
    }

    #[test]
    fn check_extern_rejects_missing_interface_query() {
        let mut interface = payment_interface();
        interface.queries.push(EQuerySig {
            name: "settlement_count".to_owned(),
            params: vec![],
            return_type: ty_int(),
            span: None,
        });
        let env = env_with_interface(interface);
        let ext = EExtern {
            name: "StripeGateway".to_owned(),
            implements: Some("PaymentProcessor".to_owned()),
            commands: vec![command("authorize", Some(ty_string()))],
            mays: vec![may("authorize", lit_string("ok"))],
            assumes: vec![],
            span: None,
        };

        let errors = check_extern(&env, &ext);

        assert!(
            errors.iter().any(|error| error.message.contains(
                "extern `StripeGateway` is missing query `settlement_count` required by interface `PaymentProcessor`"
            )),
            "expected missing extern query diagnostic, got: {errors:?}"
        );
    }

    #[test]
    fn check_extern_stops_after_unknown_interface() {
        let env = Env::new();
        let ext = EExtern {
            name: "StripeGateway".to_owned(),
            implements: Some("MissingInterface".to_owned()),
            commands: vec![command("authorize", Some(ty_string()))],
            mays: vec![],
            assumes: vec![],
            span: None,
        };

        let errors = check_extern(&env, &ext);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("unknown interface"));
    }

    #[test]
    fn check_extern_validates_may_blocks_and_assumptions() {
        let env = Env::new();
        let ext = EExtern {
            name: "StripeGateway".to_owned(),
            implements: None,
            commands: vec![
                command("authorize", Some(ty_string())),
                command("void_command", None),
                command("missing_may", Some(ty_int())),
            ],
            mays: vec![
                may("authorize", lit_string("ok")),
                may("authorize", lit_int(1)),
                may("unknown", lit_int(2)),
                may("void_command", lit_int(3)),
            ],
            assumes: vec![
                EExternAssume::Fair(vec!["Other".to_string(), "authorize".to_string()], None),
                EExternAssume::StrongFair(vec!["missing".to_string()], None),
                EExternAssume::Expr(lit_int(1), None),
                EExternAssume::Expr(
                    EExpr::Lit(Ty::Builtin(BuiltinTy::Bool), Literal::Bool(true), None),
                    None,
                ),
            ],
            span: None,
        };

        let errors = check_extern(&env, &ext);
        assert_eq!(errors.len(), 8, "unexpected extern diagnostics: {errors:?}");
        assert!(errors
            .iter()
            .any(|error| error.message.contains("multiple `may authorize`")));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("returns `int` but command")));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("unknown command `unknown`")));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("has no return type")));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("missing a `may missing_may`")));
        assert!(errors.iter().any(|error| error
            .message
            .contains("must reference a local command name")));
        assert!(errors.iter().any(|error| error
            .message
            .contains("references unknown command `missing`")));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("assume expression must be bool")));
    }

    #[test]
    fn check_extern_accepts_bool_and_poison_assume_expressions() {
        let env = Env::new();
        let ext = EExtern {
            name: "StripeGateway".to_owned(),
            implements: None,
            commands: vec![command("authorize", Some(ty_string()))],
            mays: vec![may("authorize", lit_string("ok"))],
            assumes: vec![
                EExternAssume::Expr(
                    EExpr::Lit(Ty::Builtin(BuiltinTy::Bool), Literal::Bool(true), None),
                    None,
                ),
                EExternAssume::Expr(EExpr::Var(Ty::Error, "Unknown".to_string(), None), None),
            ],
            span: None,
        };

        let errors = check_extern(&env, &ext);
        assert!(
            errors.is_empty(),
            "unexpected extern diagnostics: {errors:?}"
        );
    }

    #[test]
    fn interface_conformance_rejects_command_return_presence_mismatches() {
        let interface_requires_return = EInterface {
            name: "PaymentProcessor".to_owned(),
            commands: vec![command("authorize", Some(ty_string()))],
            queries: vec![],
            span: None,
        };
        let mut env = env_with_interface(interface_requires_return);
        let mut system = system_with_command("authorize", None);
        system.implements = Some("PaymentProcessor".to_string());
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("has no return type")));

        let interface_declares_no_return = EInterface {
            name: "PaymentProcessor".to_owned(),
            commands: vec![command("authorize", None)],
            queries: vec![],
            span: None,
        };
        env = env_with_interface(interface_declares_no_return);
        system = system_with_command("authorize", Some(ty_int()));
        system.implements = Some("PaymentProcessor".to_string());
        let errors = check_system(&env, &system);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("declares no return value")));

        system = system_with_command("authorize", Some(Ty::Error));
        system.implements = Some("PaymentProcessor".to_string());
        let errors = check_system(&env, &system);
        assert!(
            !errors
                .iter()
                .any(|error| error.message.contains("declares no return value")),
            "Ty::Error return should not trigger interface return-presence mismatch: {errors:?}"
        );
    }

    #[test]
    fn interface_conformance_rejects_query_parameter_and_return_mismatches() {
        let interface = EInterface {
            name: "PaymentProcessor".to_owned(),
            commands: vec![],
            queries: vec![EQuerySig {
                name: "settlement_count".to_owned(),
                params: vec![("merchant".to_owned(), ty_int())],
                return_type: ty_int(),
                span: None,
            }],
            span: None,
        };
        let env = env_with_interface(interface);
        let mut system = system_with_command("noop", None);
        system.commands.clear();
        system.implements = Some("PaymentProcessor".to_string());
        system.queries = vec![query(
            "settlement_count",
            vec![("merchant".to_string(), ty_string())],
            EExpr::Lit(Ty::Builtin(BuiltinTy::Bool), Literal::Bool(true), None),
        )];

        let errors = check_system(&env, &system);
        assert_eq!(errors.len(), 2);
        assert!(errors
            .iter()
            .any(|error| error.message.contains("parameter 1 has type")));
        assert!(errors
            .iter()
            .any(|error| error.message.contains("returns `bool`")));

        system.queries = vec![query(
            "settlement_count",
            vec![
                ("merchant".to_string(), ty_int()),
                ("extra".to_string(), ty_int()),
            ],
            lit_int(1),
        )];
        let errors = check_system(&env, &system);
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("has 2 parameter(s)"));
    }

    #[test]
    fn return_helpers_extract_constructor_names_and_payload_shapes() {
        let bare = enum_variant(payment_decision_ty(), "Approved");
        assert_eq!(
            extract_return_ctor_name(&bare),
            Some("Approved".to_string())
        );
        match extract_return_payload(&bare) {
            ReturnPayload::Positional(args) => assert!(args.is_empty()),
            ReturnPayload::Named(_) => panic!("bare constructor should be positional"),
        }

        let called = EExpr::Call(
            payment_decision_ty(),
            Box::new(enum_variant(payment_decision_ty(), "Declined")),
            vec![lit_int(7), lit_string("no")],
            None,
        );
        assert_eq!(
            extract_return_ctor_name(&called),
            Some("Declined".to_string())
        );
        match extract_return_payload(&called) {
            ReturnPayload::Positional(args) => assert_eq!(args.len(), 2),
            ReturnPayload::Named(_) => panic!("call constructor should be positional"),
        }

        let record = EExpr::CtorRecord(
            payment_decision_ty(),
            Some("PaymentDecision".to_string()),
            "Approved".to_string(),
            vec![
                ("code".to_string(), lit_int(200)),
                ("label".to_string(), lit_string("ok")),
            ],
            None,
        );
        assert_eq!(
            extract_return_ctor_name(&record),
            Some("Approved".to_string())
        );
        match extract_return_payload(&record) {
            ReturnPayload::Named(fields) => {
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "code");
                assert_eq!(fields[1].0, "label");
            }
            ReturnPayload::Positional(_) => panic!("record constructor should be named"),
        }

        let non_constructor = EExpr::Field(
            ty_int(),
            Box::new(EExpr::Var(ty_int(), "x".to_string(), None)),
            "value".to_string(),
            None,
        );
        assert_eq!(extract_return_ctor_name(&non_constructor), None);
        match extract_return_payload(&non_constructor) {
            ReturnPayload::Positional(args) => assert!(args.is_empty()),
            ReturnPayload::Named(_) => panic!("non-constructor fallback should be positional"),
        }
    }

    #[test]
    fn proc_dep_condition_checker_validates_nodes_and_outcome_ports() {
        let outcome_ty = Ty::Enum(
            "ChargeOutcome".to_string(),
            vec!["Approved".to_string(), "Declined".to_string()],
        );
        let proc = proc_with_node("charge");
        let node_names = HashSet::from(["charge"]);
        let let_binding_systems = HashMap::from([("payments", "Payments")]);
        let mut env = Env::new();
        env.systems.insert(
            "Payments".to_string(),
            system_with_command("charge", Some(outcome_ty)),
        );
        let ctx = ProcDepCheckCtx {
            env: &env,
            proc: &proc,
            node_names: &node_names,
            let_binding_systems: &let_binding_systems,
            proc_ctx: "proc checkout",
            span: crate::span::Span { start: 1, end: 2 },
        };

        let mut errors = Vec::new();
        validate_proc_dep_cond(
            &ctx,
            &EProcDepCond::Fact {
                node: "missing".to_string(),
                qualifier: None,
            },
            &mut errors,
        );
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("not a declared node"));

        errors.clear();
        validate_proc_dep_cond(
            &ctx,
            &EProcDepCond::Fact {
                node: "charge".to_string(),
                qualifier: Some("done".to_string()),
            },
            &mut errors,
        );
        assert!(errors.is_empty());

        validate_proc_dep_cond(
            &ctx,
            &EProcDepCond::Fact {
                node: "charge".to_string(),
                qualifier: Some("Approved".to_string()),
            },
            &mut errors,
        );
        assert!(errors.is_empty());

        validate_proc_dep_cond(
            &ctx,
            &EProcDepCond::Fact {
                node: "charge".to_string(),
                qualifier: Some("Missing".to_string()),
            },
            &mut errors,
        );
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("return type has variants"));

        let proc = proc_with_node("no_return");
        let mut no_return_env = Env::new();
        no_return_env.systems.insert(
            "Payments".to_string(),
            system_with_command("no_return", None),
        );
        let no_return_ctx = ProcDepCheckCtx {
            env: &no_return_env,
            proc: &proc,
            node_names: &node_names,
            let_binding_systems: &let_binding_systems,
            proc_ctx: "proc checkout",
            span: crate::span::Span { start: 3, end: 4 },
        };
        let mut no_return_errors = Vec::new();
        validate_proc_dep_cond(
            &no_return_ctx,
            &EProcDepCond::Fact {
                node: "charge".to_string(),
                qualifier: Some("Approved".to_string()),
            },
            &mut no_return_errors,
        );
        assert_eq!(no_return_errors.len(), 1);
        assert!(no_return_errors[0].message.contains("has no return type"));

        let proc = proc_with_node("count");
        let mut int_env = Env::new();
        int_env.systems.insert(
            "Payments".to_string(),
            system_with_command("count", Some(ty_int())),
        );
        let int_ctx = ProcDepCheckCtx {
            env: &int_env,
            proc: &proc,
            node_names: &node_names,
            let_binding_systems: &let_binding_systems,
            proc_ctx: "proc checkout",
            span: crate::span::Span { start: 5, end: 6 },
        };
        let mut int_errors = Vec::new();
        validate_proc_dep_cond(
            &int_ctx,
            &EProcDepCond::Fact {
                node: "charge".to_string(),
                qualifier: Some("Approved".to_string()),
            },
            &mut int_errors,
        );
        assert_eq!(int_errors.len(), 1);
        assert!(int_errors[0].message.contains("not an enum"));
    }
}
