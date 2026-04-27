//! System well-formedness checking.

use std::collections::{HashMap, HashSet};

use super::super::env::Env;
use super::super::error::{ElabError, ErrorKind};
use super::super::types::{
    EEventAction, EExpr, EExtern, EExternAssume, EMatchScrutinee, EProcDepCond, ESystem, Ty,
};

pub(super) fn check_system(env: &Env, system: &ESystem) -> Vec<ElabError> {
    let mut errors = Vec::new();
    let sys_ctx = format!("system {}", system.name);

    let entity_names: Vec<String> = env.entities.keys().cloned().collect();
    // Also accept canonical entity names (the entity's declared name may differ
    // from the working namespace key when imported via alias).
    let canonical_names: std::collections::HashSet<String> =
        env.entities.values().map(|e| e.name.clone()).collect();
    for (_, entity_name) in &system.store_params {
        if env.lookup_entity(entity_name).is_none() && !canonical_names.contains(entity_name) {
            let mut err = if let Some(span) = system.span {
                ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!("system {} uses unknown entity '{entity_name}'", system.name),
                    &sys_ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::UndefinedRef,
                    format!("system {} uses unknown entity '{entity_name}'", system.name),
                    &sys_ctx,
                )
            };
            if let Some(closest) = super::find_closest_name(entity_name, &entity_names) {
                err = err.with_help(format!("did you mean '{closest}'?"));
            }
            errors.push(err);
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
            errors.push(ElabError::with_span(
                ErrorKind::UndefinedRef,
                format!(
                    "system `{}` declares unknown extern dep `{dep}`",
                    system.name
                ),
                &sys_ctx,
                system
                    .span
                    .unwrap_or(crate::span::Span { start: 0, end: 0 }),
            ));
        }
    }

    if let Some(interface_name) = &system.implements {
        let Some(interface) = env.interfaces.get(interface_name) else {
            let err = if let Some(span) = system.span {
                ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!(
                        "system {} implements unknown interface `{interface_name}`",
                        system.name
                    ),
                    &sys_ctx,
                    span,
                )
            } else {
                ElabError::new(
                    ErrorKind::UndefinedRef,
                    format!(
                        "system {} implements unknown interface `{interface_name}`",
                        system.name
                    ),
                    &sys_ctx,
                )
            };
            errors.push(err);
            return errors;
        };

        for iface_cmd in &interface.commands {
            match system
                .commands
                .iter()
                .find(|cmd| cmd.name == iface_cmd.name)
            {
                Some(sys_cmd) => {
                    if sys_cmd.params.len() != iface_cmd.params.len() {
                        errors.push(ElabError::with_span(
                            ErrorKind::ParamMismatch,
                            format!(
                                "system `{}` command `{}` has {} parameter(s), but interface `{}` requires {}",
                                system.name,
                                iface_cmd.name,
                                sys_cmd.params.len(),
                                interface.name,
                                iface_cmd.params.len()
                            ),
                            &sys_ctx,
                            sys_cmd.span.or(system.span).unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    } else {
                        for (idx, (sys_param, iface_param)) in sys_cmd
                            .params
                            .iter()
                            .zip(iface_cmd.params.iter())
                            .enumerate()
                        {
                            if format!("{:?}", sys_param.1) != format!("{:?}", iface_param.1) {
                                errors.push(ElabError::with_span(
                                    ErrorKind::TypeMismatch,
                                    format!(
                                        "system `{}` command `{}` parameter {} has type `{}` but interface `{}` requires `{}`",
                                        system.name,
                                        iface_cmd.name,
                                        idx + 1,
                                        sys_param.1.name(),
                                        interface.name,
                                        iface_param.1.name()
                                    ),
                                    &sys_ctx,
                                    sys_cmd.span.or(system.span).unwrap_or(crate::span::Span { start: 0, end: 0 }),
                                ));
                            }
                        }
                    }
                    match (&sys_cmd.return_type, &iface_cmd.return_type) {
                        (Some(sys_ret), Some(iface_ret))
                            if !matches!(sys_ret, Ty::Error)
                                && !matches!(iface_ret, Ty::Error)
                                && !super::types_compatible(sys_ret, iface_ret) =>
                        {
                            errors.push(ElabError::with_span(
                                ErrorKind::TypeMismatch,
                                format!(
                                    "system `{}` command `{}` returns `{}` but interface `{}` requires `{}`",
                                    system.name,
                                    iface_cmd.name,
                                    sys_ret.name(),
                                    interface.name,
                                    iface_ret.name()
                                ),
                                &sys_ctx,
                                sys_cmd.span.or(system.span).unwrap_or(crate::span::Span { start: 0, end: 0 }),
                            ));
                        }
                        (None, Some(iface_ret)) => {
                            errors.push(ElabError::with_span(
                                ErrorKind::TypeMismatch,
                                format!(
                                    "system `{}` command `{}` has no return type but interface `{}` requires `{}`",
                                    system.name,
                                    iface_cmd.name,
                                    interface.name,
                                    iface_ret.name()
                                ),
                                &sys_ctx,
                                sys_cmd.span.or(system.span).unwrap_or(crate::span::Span { start: 0, end: 0 }),
                            ));
                        }
                        _ => {}
                    }
                }
                None => {
                    errors.push(ElabError::with_span(
                        ErrorKind::UndefinedRef,
                        format!(
                            "system `{}` is missing command `{}` required by interface `{}`",
                            system.name, iface_cmd.name, interface.name
                        ),
                        &sys_ctx,
                        system
                            .span
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                }
            }
        }

        for iface_query in &interface.queries {
            match system.queries.iter().find(|q| q.name == iface_query.name) {
                Some(sys_query) => {
                    if sys_query.params.len() != iface_query.params.len() {
                        errors.push(ElabError::with_span(
                            ErrorKind::ParamMismatch,
                            format!(
                                "system `{}` query `{}` has {} parameter(s), but interface `{}` requires {}",
                                system.name,
                                iface_query.name,
                                sys_query.params.len(),
                                interface.name,
                                iface_query.params.len()
                            ),
                            &sys_ctx,
                            sys_query.span.or(system.span).unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    } else {
                        for (idx, (sys_param, iface_param)) in sys_query
                            .params
                            .iter()
                            .zip(iface_query.params.iter())
                            .enumerate()
                        {
                            if format!("{:?}", sys_param.1) != format!("{:?}", iface_param.1) {
                                errors.push(ElabError::with_span(
                                    ErrorKind::TypeMismatch,
                                    format!(
                                        "system `{}` query `{}` parameter {} has type `{}` but interface `{}` requires `{}`",
                                        system.name,
                                        iface_query.name,
                                        idx + 1,
                                        sys_param.1.name(),
                                        interface.name,
                                        iface_param.1.name()
                                    ),
                                    &sys_ctx,
                                    sys_query.span.or(system.span).unwrap_or(crate::span::Span { start: 0, end: 0 }),
                                ));
                            }
                        }
                    }

                    let sys_ret = sys_query.body.ty();
                    let iface_ret = &iface_query.return_type;
                    if !matches!(&sys_ret, Ty::Error)
                        && !matches!(iface_ret, Ty::Error)
                        && !super::types_compatible(&sys_ret, iface_ret)
                    {
                        errors.push(ElabError::with_span(
                            ErrorKind::TypeMismatch,
                            format!(
                                "system `{}` query `{}` returns `{}` but interface `{}` requires `{}`",
                                system.name,
                                iface_query.name,
                                sys_ret.name(),
                                interface.name,
                                iface_ret.name()
                            ),
                            &sys_ctx,
                            sys_query.span.or(system.span).unwrap_or(crate::span::Span { start: 0, end: 0 }),
                        ));
                    }
                }
                None => {
                    errors.push(ElabError::with_span(
                        ErrorKind::UndefinedRef,
                        format!(
                            "system `{}` is missing query `{}` required by interface `{}`",
                            system.name, iface_query.name, interface.name
                        ),
                        &sys_ctx,
                        system
                            .span
                            .unwrap_or(crate::span::Span { start: 0, end: 0 }),
                    ));
                }
            }
        }
    }

    for step in &system.steps {
        validate_crosscalls_in_actions(
            env,
            &system.name,
            &sys_ctx,
            &system.deps,
            &step.body,
            &mut errors,
            step.span.or(system.span),
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
        super::check_invariant_body_no_liveness(&inv.body, &mut errors);
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
    for step in &system.steps {
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
                        "step `{}` has a `return` expression but command `{}` \
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
                                                    "step `{}` returns `@{name}` with argument {} \
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
                                            "step `{}` returns `@{name}` with {} \
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
                                            "step `{}` returns `@{name}` with {} \
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
                                                    "step `{}` returns `@{name}` with field \
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
                                                "step `{}` returns `@{name}` with unknown \
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
                                "step `{}` returns `@{name}` which is not a variant of \
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
                            "step `{}` returns a non-constructor expression but \
                             command `{}` expects return type `{enum_name}` \
                             (an enum); use `return @variant` or `return @variant(...)`",
                            step.name, step.name
                        ),
                        &sys_ctx,
                        step_span,
                    ));
                }
            }
            // Both present but return type is not enum — can't validate
            // constructor form; accept for now (non-enum return types are
            // future work).
            (Some(_), Some(_)) => {}
            _ => {}
        }
    }

    // validate proc declarations.
    // Build let-binding map: instance_name → system_type
    let let_binding_systems: HashMap<&str, &str> = system
        .let_bindings
        .iter()
        .map(|lb| (lb.name.as_str(), lb.system_type.as_str()))
        .collect();
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
                        "proc node `{}` references instance `{}` which is not a let binding in this program",
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

pub(super) fn check_extern(_env: &Env, ext: &EExtern) -> Vec<ElabError> {
    let mut errors = Vec::new();
    let ext_ctx = format!("extern {}", ext.name);

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
                    if !matches!(ret_ty, Ty::Error) && !super::types_compatible(&ret_ty, return_ty)
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

fn validate_crosscalls_in_actions(
    env: &Env,
    system_name: &str,
    sys_ctx: &str,
    deps: &[String],
    actions: &[EEventAction],
    errors: &mut Vec<ElabError>,
    fallback_span: Option<crate::span::Span>,
) {
    for action in actions {
        match action {
            EEventAction::Choose(_, _, _, body) | EEventAction::ForAll(_, _, body) => {
                validate_crosscalls_in_actions(
                    env,
                    system_name,
                    sys_ctx,
                    deps,
                    body,
                    errors,
                    fallback_span,
                );
            }
            EEventAction::LetCrossCall(_, target, command, args) => {
                validate_crosscall_target(
                    env,
                    system_name,
                    sys_ctx,
                    deps,
                    target,
                    command,
                    args,
                    errors,
                    fallback_span,
                );
            }
            EEventAction::CrossCall(target, command, args) => {
                validate_crosscall_target(
                    env,
                    system_name,
                    sys_ctx,
                    deps,
                    target,
                    command,
                    args,
                    errors,
                    fallback_span,
                );
            }
            EEventAction::Match(scrutinee, arms) => {
                if let EMatchScrutinee::CrossCall(target, command, args) = scrutinee {
                    validate_crosscall_target(
                        env,
                        system_name,
                        sys_ctx,
                        deps,
                        target,
                        command,
                        args,
                        errors,
                        fallback_span,
                    );
                }
                for arm in arms {
                    validate_crosscalls_in_actions(
                        env,
                        system_name,
                        sys_ctx,
                        deps,
                        &arm.body,
                        errors,
                        fallback_span,
                    );
                }
            }
            EEventAction::Create(_, _, _)
            | EEventAction::Apply(_, _, _, _)
            | EEventAction::Expr(_) => {}
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn validate_crosscall_target(
    env: &Env,
    system_name: &str,
    sys_ctx: &str,
    deps: &[String],
    target: &str,
    command: &str,
    args: &[EExpr],
    errors: &mut Vec<ElabError>,
    fallback_span: Option<crate::span::Span>,
) {
    let is_system = env.systems.contains_key(target);
    let is_extern = env.externs.contains_key(target);
    let span = fallback_span.unwrap_or(crate::span::Span { start: 0, end: 0 });

    if is_system && is_extern {
        errors.push(ElabError::with_span(
            ErrorKind::AmbiguousRef,
            format!("cross-call target `{target}` is ambiguous between a system and an extern"),
            sys_ctx,
            span,
        ));
        return;
    }

    if is_extern {
        if !deps.iter().any(|dep| dep == target) {
            errors.push(ElabError::with_span(
                ErrorKind::InvalidScope,
                format!("system `{system_name}` calls extern `{target}` without declaring `dep {target}`"),
                sys_ctx,
                span,
            ));
            return;
        }

        if let Some(ext) = env.externs.get(target) {
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
                            sys_ctx,
                            span,
                        ));
                    }
                }
                None => errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!("extern `{target}` has no command `{command}`"),
                    sys_ctx,
                    span,
                )),
            }
        }
    } else if is_system {
        if let Some(target_sys) = env.systems.get(target) {
            let matching_steps: Vec<_> = target_sys
                .steps
                .iter()
                .filter(|step| step.name == *command)
                .collect();
            if matching_steps.is_empty() {
                errors.push(ElabError::with_span(
                    ErrorKind::UndefinedRef,
                    format!("system `{target}` has no command `{command}`"),
                    sys_ctx,
                    span,
                ));
            } else {
                for step in matching_steps {
                    if step.params.len() != args.len() {
                        errors.push(ElabError::with_span(
                            ErrorKind::ParamMismatch,
                            format!(
                                "cross-call `{target}::{command}` expects {} args but got {}",
                                step.params.len(),
                                args.len()
                            ),
                            sys_ctx,
                            span,
                        ));
                    }
                }
            }
        }
    } else {
        errors.push(ElabError::with_span(
            ErrorKind::UndefinedRef,
            format!("cross-call target `{target}` is not a known system or extern"),
            sys_ctx,
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
        | EExpr::SetComp(_, _, _, _, _, span)
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
        EExpr::Var(..) => ReturnPayload::Positional(vec![]),
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
